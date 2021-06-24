use std::cmp::Ordering;
use std::collections::btree_map::IntoIter;
use std::collections::BTreeMap;
use std::convert::TryFrom;
use std::iter;

use pyo3::class::iter::{IterNextOutput, PyIterProtocol};
use pyo3::conversion::{ToBorrowedObject, ToPyObject};
use pyo3::types::PyDict;
use pyo3::{prelude::*, PyMappingProtocol, PyNativeType, PyObjectProtocol};

type Hash = isize;

#[pyclass]
#[derive(Debug, Clone, Default)]
pub struct Dict {
    map: BTreeMap<Hash, BTreeMap<Hash, (PyObject, PyObject)>>,
}

impl TryFrom<&PyDict> for Dict {
    type Error = PyErr;
    fn try_from(dict: &PyDict) -> PyResult<Self> {
        let mut map = Dict::new();
        for (k, v) in dict {
            map.set_item(dict.py(), k, v)?;
        }
        Ok(map)
    }
}

fn as_dict_obj(py: Python, obj: PyObject) -> PyResult<PyObject> {
    let obj = obj.into_ref(py);
    let obj = if obj.is_instance::<PyDict>()? {
        Dict::try_from(obj.downcast::<PyDict>()?)?.into_py(py)
    } else {
        obj.to_object(py)
    };
    Ok(obj)
}

impl Dict {
    fn is_eq(py: Python, a: &PyObject, b: &PyObject) -> bool {
        a.as_ref(py)
            .compare(b.as_ref(py))
            .map(|ord| Ordering::Equal == ord)
            .unwrap_or(false)
    }

    pub fn set_item<K: ToPyObject, V: ToPyObject>(
        &mut self,
        py: Python,
        k: K,
        v: V,
    ) -> PyResult<()> {
        let k = as_dict_obj(py, k.to_object(py))?;
        let v = as_dict_obj(py, v.to_object(py))?;
        let k_hash = k.as_ref(py).hash()?;
        let v_hash = k.as_ref(py).hash()?;
        self.map.entry(k_hash).or_default().insert(v_hash, (k, v));
        Ok(())
    }

    pub fn get_item<K: ToBorrowedObject>(&self, py: Python, k: K) -> PyResult<Option<PyObject>> {
        let k = as_dict_obj(py, k.to_object(py))?;
        let k_hash = k.as_ref(py).hash()?;
        let bucket = match self.map.get(&k_hash) {
            Some(bucket) => bucket,
            None => return Ok(None),
        };
        Ok(bucket
            .values()
            .find(|(bucket_k, _)| Self::is_eq(py, &k, bucket_k))
            .map(|(_, v)| v.clone()))
    }

    fn remove_item<K: ToBorrowedObject>(&mut self, py: Python, k: K) -> PyResult<Option<PyObject>> {
        let k = as_dict_obj(py, k.to_object(py))?;
        let k_hash = k.as_ref(py).hash()?;
        let bucket = match self.map.get_mut(&k_hash) {
            Some(bucket) => bucket,
            None => return Ok(None),
        };
        Ok(bucket
            .values_mut()
            .find(|(bucket_k, _)| Self::is_eq(py, &k, bucket_k))
            .map(|(_, v)| v.clone()))
    }

    pub fn iter<'py>(
        &'py self,
        py: Python<'py>,
    ) -> impl Iterator<Item = (&'py PyAny, &'py PyAny)> + 'py {
        self.map
            .values()
            .flat_map(BTreeMap::values)
            .map(move |(k, v)| (k.clone().into_ref(py), v.clone().into_ref(py)))
    }

    pub fn into_iter(self, py: Python<'_>) -> impl Iterator<Item = (&'_ PyAny, &'_ PyAny)> {
        self.map
            .into_iter()
            .flat_map(|(_, bucket)| bucket.into_iter())
            .map(move |(_, (k, v))| (k.into_ref(py), v.into_ref(py)))
    }

    pub fn keys<'py>(&'py self, py: Python<'py>) -> impl Iterator<Item = &'py PyAny> + 'py {
        self.iter(py).map(|(k, _)| k)
    }

    pub fn into_keys(self, py: Python<'_>) -> impl Iterator<Item = &'_ PyAny> {
        self.into_iter(py).map(|(k, _)| k)
    }

    pub fn values<'py>(&'py self, py: Python<'py>) -> impl Iterator<Item = &'py PyAny> + 'py {
        self.iter(py).map(|(_, v)| v)
    }

    pub fn into_values(self, py: Python<'_>) -> impl Iterator<Item = &'_ PyAny> {
        self.into_iter(py).map(|(_, v)| v)
    }

    pub fn hash(&self, py: Python) -> Hash {
        let sum_hash =
            |a: isize, b: isize| a.wrapping_add(b).into_py(py).as_ref(py).hash().unwrap();

        self.map
            .iter()
            .flat_map(|(key, bucket)| bucket.keys().copied().zip(iter::repeat(*key)))
            .fold(0, |prev, (value, key)| sum_hash(prev, sum_hash(value, key)))
    }

    pub fn len(&self) -> usize {
        self.map.iter().fold(0, |prev, (_, next)| prev + next.len())
    }

    pub fn is_empty(&self) -> bool {
        self.map.len() == 0
    }
}

#[pymethods]
impl Dict {
    #[new]
    pub fn new() -> Self {
        Self::default()
    }

    #[name = "keys"]
    fn _keys(&self) -> Keys {
        Keys::new(self.clone())
    }

    #[name = "values"]
    fn _values(&self) -> Values {
        Values::new(self.clone())
    }

    fn items(&self) -> Items {
        Items::new(self.clone())
    }
}

#[pyproto]
impl PyObjectProtocol for Dict {
    fn __hash__(&self) -> isize {
        Python::with_gil(|py| self.hash(py))
    }

    fn __str__(&self) -> PyResult<String> {
        Python::with_gil(|py| {
            let items = self
                .iter(py)
                .map(|(k, v)| Ok(format!("{}: {}", k.str()?, v.str()?)))
                .collect::<PyResult<Vec<_>>>()?
                .join(",");
            Ok(format!("{{{}}}", items))
        })
    }

    fn __repr__(&self) -> PyResult<String> {
        Python::with_gil(|py| {
            let items = self
                .iter(py)
                .map(|(k, v)| Ok(format!("{}: {}", k.repr()?, v.repr()?)))
                .collect::<PyResult<Vec<_>>>()?
                .join(",");
            Ok(format!("{{{}}}", items))
        })
    }
}

#[pyproto]
impl PyMappingProtocol for Dict {
    fn __len__(&self) -> usize {
        self.len()
    }

    fn __setitem__(&mut self, key: PyObject, value: PyObject) -> PyResult<()> {
        Python::with_gil(|py| self.set_item(py, key, value))
    }

    fn __delitem__(&mut self, key: PyObject) -> PyResult<()> {
        Python::with_gil(|py| self.remove_item(py, key))?;
        Ok(())
    }

    fn __getitem__(&self, key: PyObject) -> PyResult<Option<PyObject>> {
        Python::with_gil(|py| self.get_item(py, key))
    }
}

#[pyclass]
struct Items {
    dict: IntoIter<Hash, BTreeMap<Hash, (PyObject, PyObject)>>,
    bucket: Option<IntoIter<Hash, (PyObject, PyObject)>>,
}

impl Items {
    fn new(dict: Dict) -> Self {
        Self {
            dict: dict.map.into_iter(),
            bucket: None,
        }
    }

    fn next(&mut self) -> Option<(PyObject, PyObject)> {
        if let Some(bucket) = &mut self.bucket {
            if let Some((_, entry)) = bucket.next() {
                return Some(entry);
            }
        }
        self.bucket = match self.dict.next() {
            Some((_, bucket)) => Some(bucket.into_iter()),
            None => return None,
        };

        self.next()
    }
}

#[pyclass]
struct Keys {
    items: Items,
}

impl Keys {
    fn new(dict: Dict) -> Self {
        let items = Items::new(dict);
        Self { items }
    }
}

#[pyclass]
struct Values {
    items: Items,
}

impl Values {
    fn new(dict: Dict) -> Self {
        let items = Items::new(dict);
        Self { items }
    }
}

#[pyproto]
impl PyIterProtocol for Items {
    fn __next__(mut slf: PyRefMut<Self>) -> IterNextOutput<(PyObject, PyObject), ()> {
        match slf.next() {
            Some(entry) => IterNextOutput::Yield(entry),
            None => IterNextOutput::Return(()),
        }
    }
}

#[pyproto]
impl PyIterProtocol for Keys {
    fn __next__(mut slf: PyRefMut<Self>) -> IterNextOutput<PyObject, ()> {
        match slf.items.next() {
            Some((entry, _)) => IterNextOutput::Yield(entry),
            None => IterNextOutput::Return(()),
        }
    }
}

#[pyproto]
impl PyIterProtocol for Values {
    fn __next__(mut slf: PyRefMut<Self>) -> IterNextOutput<PyObject, ()> {
        match slf.items.next() {
            Some((_, entry)) => IterNextOutput::Yield(entry),
            None => IterNextOutput::Return(()),
        }
    }
}
