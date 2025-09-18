// <vc-preamble>
use vstd::prelude::*;

verus! {

#[derive(PartialEq, Eq, Structural)]
pub enum NumpyDType {

    Int8,

    Int16,

    Int32,

    Int64,

    Float32,

    Float64,

    Complex64,

    Complex128,

    Bool,
}

spec fn type_rank(dtype: NumpyDType) -> nat {
    match dtype {
        NumpyDType::Bool => 0,
        NumpyDType::Int8 => 1,
        NumpyDType::Int16 => 2,
        NumpyDType::Int32 => 3,
        NumpyDType::Int64 => 4,
        NumpyDType::Float32 => 5,
        NumpyDType::Float64 => 6,
        NumpyDType::Complex64 => 7,
        NumpyDType::Complex128 => 8,
    }
}

pub enum NumpyOperand {

    Scalar(NumpyDType),

    Array(NumpyDType, Vec<i32>),
}

spec fn operand_type(operand: NumpyOperand) -> NumpyDType {
    match operand {
        NumpyOperand::Scalar(dtype) => dtype,
        NumpyOperand::Array(dtype, _) => dtype,
    }
}

spec fn promote_types(t1: NumpyDType, t2: NumpyDType) -> NumpyDType {
    if type_rank(t1) >= type_rank(t2) { t1 } else { t2 }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Use plain nat values instead of nat suffix */
fn exec_type_rank(dtype: NumpyDType) -> (rank: nat)
    ensures rank == type_rank(dtype)
{
    match dtype {
        NumpyDType::Bool => 0,
        NumpyDType::Int8 => 1,
        NumpyDType::Int16 => 2,
        NumpyDType::Int32 => 3,
        NumpyDType::Int64 => 4,
        NumpyDType::Float32 => 5,
        NumpyDType::Float64 => 6,
        NumpyDType::Complex64 => 7,
        NumpyDType::Complex128 => 8,
    }
}
// </vc-helpers>

// <vc-spec>
fn result_type(operands: Vec<NumpyOperand>) -> (result: NumpyDType)
    requires operands.len() > 0,
    ensures

        forall|i: int| 0 <= i < operands.len() ==> 
            type_rank(result) >= type_rank(operand_type(operands[i])),

        exists|i: int| 0 <= i < operands.len() && 
            type_rank(result) == type_rank(operand_type(operands[i])),

        forall|i: int, j: int| 0 <= i < operands.len() && 0 <= j < operands.len() ==>
            type_rank(result) >= type_rank(promote_types(operand_type(operands[i]), operand_type(operands[j]))),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Use exec_type_rank for runtime comparison */
    let mut result = match operands[0] {
        NumpyOperand::Scalar(dtype) => dtype,
        NumpyOperand::Array(dtype, _) => dtype,
    };
    let mut i: usize = 1;
    while i < operands.len()
        invariant
            i <= operands.len(),
            forall|j: int| 0 <= j < i ==> type_rank(result) >= type_rank(operand_type(operands[j])),
            exists|j: int| 0 <= j < i && type_rank(result) == type_rank(operand_type(operands[j])),
            forall|j: int, k: int| 0 <= j < i && 0 <= k < i ==> type_rank(result) >= type_rank(promote_types(operand_type(operands[j]), operand_type(operands[k]))),
    {
        let current_type = match operands[i] {
            NumpyOperand::Scalar(dtype) => dtype,
            NumpyOperand::Array(dtype, _) => dtype,
        };
        result = if exec_type_rank(result) >= exec_type_rank(current_type) { result } else { current_type };
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}