// <vc-preamble>
use vstd::prelude::*;

verus! {

#[derive(PartialEq, Eq)]
pub enum NumpyDType {

    Bool,

    Int8,

    Int16,

    Int32,

    Int64,

    UInt8,

    UInt16,

    UInt32,

    UInt64,

    Float16,

    Float32,

    Float64,

    Complex64,

    Complex128,
}

#[derive(PartialEq, Eq)]
pub enum DTypeKind {

    Bool,

    SignedInteger,

    UnsignedInteger,

    Integral,

    RealFloating,

    ComplexFloating,

    Numeric,
}

spec fn get_dtype_kind(dtype: NumpyDType) -> DTypeKind {
    match dtype {
        NumpyDType::Bool => DTypeKind::Bool,
        NumpyDType::Int8 | NumpyDType::Int16 | NumpyDType::Int32 | NumpyDType::Int64 => DTypeKind::SignedInteger,
        NumpyDType::UInt8 | NumpyDType::UInt16 | NumpyDType::UInt32 | NumpyDType::UInt64 => DTypeKind::UnsignedInteger,
        NumpyDType::Float16 | NumpyDType::Float32 | NumpyDType::Float64 => DTypeKind::RealFloating,
        NumpyDType::Complex64 | NumpyDType::Complex128 => DTypeKind::ComplexFloating,
    }
}

spec fn is_of_kind(dtype: NumpyDType, kind: DTypeKind) -> bool {
    match kind {
        DTypeKind::Bool => get_dtype_kind(dtype) == DTypeKind::Bool,
        DTypeKind::SignedInteger => get_dtype_kind(dtype) == DTypeKind::SignedInteger,
        DTypeKind::UnsignedInteger => get_dtype_kind(dtype) == DTypeKind::UnsignedInteger,
        DTypeKind::Integral => get_dtype_kind(dtype) == DTypeKind::SignedInteger || get_dtype_kind(dtype) == DTypeKind::UnsignedInteger,
        DTypeKind::RealFloating => get_dtype_kind(dtype) == DTypeKind::RealFloating,
        DTypeKind::ComplexFloating => get_dtype_kind(dtype) == DTypeKind::ComplexFloating,
        DTypeKind::Numeric => get_dtype_kind(dtype) == DTypeKind::Bool || 
                             get_dtype_kind(dtype) == DTypeKind::SignedInteger || 
                             get_dtype_kind(dtype) == DTypeKind::UnsignedInteger || 
                             get_dtype_kind(dtype) == DTypeKind::RealFloating || 
                             get_dtype_kind(dtype) == DTypeKind::ComplexFloating,
    }
}
// </vc-preamble>

// <vc-helpers>

proof fn lemma_dtype_kind_matches(dtype: NumpyDType, kind: DTypeKind)
    ensures
        is_of_kind(dtype, kind) == (
            match kind {
                DTypeKind::Bool => get_dtype_kind(dtype) == DTypeKind::Bool,
                DTypeKind::SignedInteger => get_dtype_kind(dtype) == DTypeKind::SignedInteger,
                DTypeKind::UnsignedInteger => get_dtype_kind(dtype) == DTypeKind::UnsignedInteger,
                DTypeKind::Integral => get_dtype_kind(dtype) == DTypeKind::SignedInteger || get_dtype_kind(dtype) == DTypeKind::UnsignedInteger,
                DTypeKind::RealFloating => get_dtype_kind(dtype) == DTypeKind::RealFloating,
                DTypeKind::ComplexFloating => get_dtype_kind(dtype) == DTypeKind::ComplexFloating,
                DTypeKind::Numeric => get_dtype_kind(dtype) == DTypeKind::Bool || 
                                     get_dtype_kind(dtype) == DTypeKind::SignedInteger || 
                                     get_dtype_kind(dtype) == DTypeKind::UnsignedInteger || 
                                     get_dtype_kind(dtype) == DTypeKind::RealFloating || 
                                     get_dtype_kind(dtype) == DTypeKind::ComplexFloating,
            }
        )
{
    /* helper modified by LLM (iteration 2): Fixed Numeric case to match is_of_kind spec */
}

// </vc-helpers>

// <vc-spec>
fn numpy_isdtype(dtype: NumpyDType, kind: DTypeKind) -> (result: bool)
    ensures result == is_of_kind(dtype, kind)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Replaced direct enum comparisons with pattern matching to avoid external function error */
    match kind {
        DTypeKind::Bool => matches!(dtype, NumpyDType::Bool),
        DTypeKind::SignedInteger => matches!(dtype, NumpyDType::Int8 | NumpyDType::Int16 | NumpyDType::Int32 | NumpyDType::Int64),
        DTypeKind::UnsignedInteger => matches!(dtype, NumpyDType::UInt8 | NumpyDType::UInt16 | NumpyDType::UInt32 | NumpyDType::UInt64),
        DTypeKind::Integral => matches!(dtype, NumpyDType::Int8 | NumpyDType::Int16 | NumpyDType::Int32 | NumpyDType::Int64 | NumpyDType::UInt8 | NumpyDType::UInt16 | NumpyDType::UInt32 | NumpyDType::UInt64),
        DTypeKind::RealFloating => matches!(dtype, NumpyDType::Float16 | NumpyDType::Float32 | NumpyDType::Float64),
        DTypeKind::ComplexFloating => matches!(dtype, NumpyDType::Complex64 | NumpyDType::Complex128),
        DTypeKind::Numeric => matches!(dtype, NumpyDType::Bool | NumpyDType::Int8 | NumpyDType::Int16 | NumpyDType::Int32 | NumpyDType::Int64 | NumpyDType::UInt8 | NumpyDType::UInt16 | NumpyDType::UInt32 | NumpyDType::UInt64 | NumpyDType::Float16 | NumpyDType::Float32 | NumpyDType::Float64 | NumpyDType::Complex64 | NumpyDType::Complex128),
    }
}
// </vc-code>

}
fn main() {}