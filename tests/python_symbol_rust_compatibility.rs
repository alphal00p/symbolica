#![cfg(feature = "python_export")]

use pyo3::{
    Bound, Py, PyAny, PyResult, Python,
    types::{PyTuple, PyType},
};
use symbolica::api::python::{PythonExpression, PythonTransformer, PythonUserData};

#[allow(dead_code, clippy::too_many_arguments)]
fn pinned_spynso_call_shape(
    cls: &Bound<'_, PyType>,
    py: Python,
    names: &Bound<'_, PyTuple>,
    normalization: Option<PythonTransformer>,
    print: Option<Py<PyAny>>,
    derivative: Option<Py<PyAny>>,
    series: Option<Py<PyAny>>,
    eval: Option<Py<PyAny>>,
    data: Option<PythonUserData>,
) -> PyResult<Py<PyAny>> {
    PythonExpression::symbol(
        cls,
        py,
        names,
        None,
        None,
        None,
        None,
        None,
        None,
        None,
        None,
        None,
        None,
        None,
        normalization,
        print,
        derivative,
        series,
        eval,
        data,
    )
}
