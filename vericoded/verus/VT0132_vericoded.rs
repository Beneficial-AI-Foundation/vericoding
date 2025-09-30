// <vc-preamble>
use vstd::prelude::*;

verus! {

#[derive(PartialEq, Eq)]
pub enum NumpyScalarType {
    Int32,
    Int64,
    Float32,
    Float64,
    Complex64,
    Complex128,
    Object,
    String,
    Bool,
}

pub enum NumpyObject {
    IntVal(i64),
    FloatVal(f64),
    ArrayInt(Vec<i64>),
    ArrayFloat(Vec<f64>),
    ArrayComplex(Vec<(f64, f64)>),
    GenericObj,
    StringVal(String),
    BoolVal(bool),
}

pub open spec fn matches_scalar_type(obj: NumpyObject, dtype: NumpyScalarType) -> bool {
    match (obj, dtype) {
        (NumpyObject::IntVal(_), NumpyScalarType::Int64) => true,
        (NumpyObject::FloatVal(_), NumpyScalarType::Float64) => true,
        (NumpyObject::StringVal(_), NumpyScalarType::String) => true,
        (NumpyObject::BoolVal(_), NumpyScalarType::Bool) => true,
        _ => false,
    }
}

pub open spec fn is_array_with_element_type(obj: NumpyObject, dtype: NumpyScalarType) -> bool {
    match (obj, dtype) {
        (NumpyObject::ArrayInt(_), NumpyScalarType::Int64) => true,
        (NumpyObject::ArrayFloat(_), NumpyScalarType::Float64) => true,
        (NumpyObject::ArrayComplex(_), NumpyScalarType::Complex128) => true,
        _ => false,
    }
}

pub open spec fn is_generic_object(obj: NumpyObject) -> bool {
    match obj {
        NumpyObject::GenericObj => true,
        _ => false,
    }
}
// </vc-preamble>

// <vc-helpers>
pub open spec fn inferred_dtype_no_default(rep: NumpyObject) -> Option<NumpyScalarType> {
    match rep {
        NumpyObject::IntVal(_) => Some(NumpyScalarType::Int64),
        NumpyObject::FloatVal(_) => Some(NumpyScalarType::Float64),
        NumpyObject::ArrayInt(_) => Some(NumpyScalarType::Int64),
        NumpyObject::ArrayFloat(_) => Some(NumpyScalarType::Float64),
        NumpyObject::ArrayComplex(_) => Some(NumpyScalarType::Complex128),
        NumpyObject::StringVal(_) => Some(NumpyScalarType::String),
        NumpyObject::BoolVal(_) => Some(NumpyScalarType::Bool),
        NumpyObject::GenericObj => None,
    }
}
// </vc-helpers>

// <vc-spec>
fn obj2sctype(rep: NumpyObject, default: Option<NumpyScalarType>) -> (result: Option<NumpyScalarType>)
    ensures
        match rep {
            NumpyObject::IntVal(_) => result == Some(NumpyScalarType::Int64),
            NumpyObject::FloatVal(_) => result == Some(NumpyScalarType::Float64),
            NumpyObject::ArrayInt(_) => result == Some(NumpyScalarType::Int64),
            NumpyObject::ArrayFloat(_) => result == Some(NumpyScalarType::Float64),
            NumpyObject::ArrayComplex(_) => result == Some(NumpyScalarType::Complex128),
            NumpyObject::StringVal(_) => result == Some(NumpyScalarType::String),
            NumpyObject::BoolVal(_) => result == Some(NumpyScalarType::Bool),
            NumpyObject::GenericObj => result == default,
        },
        match result {
            Some(dtype) => 
                matches_scalar_type(rep, dtype) || 
                is_array_with_element_type(rep, dtype) ||
                (is_generic_object(rep) && result == default),
            None => is_generic_object(rep) && default.is_None(),
        }
// </vc-spec>
// <vc-code>
{
    let res = match rep {
        NumpyObject::IntVal(_) => Some(NumpyScalarType::Int64),
        NumpyObject::FloatVal(_) => Some(NumpyScalarType::Float64),
        NumpyObject::ArrayInt(_) => Some(NumpyScalarType::Int64),
        NumpyObject::ArrayFloat(_) => Some(NumpyScalarType::Float64),
        NumpyObject::ArrayComplex(_) => Some(NumpyScalarType::Complex128),
        NumpyObject::StringVal(_) => Some(NumpyScalarType::String),
        NumpyObject::BoolVal(_) => Some(NumpyScalarType::Bool),
        NumpyObject::GenericObj => default,
    };
    res
}
// </vc-code>

}
fn main() {}