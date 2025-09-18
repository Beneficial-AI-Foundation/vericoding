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
/* helper modified by LLM (iteration 5): compute maximum operand type via recursion */
spec fn max_type_from(i: int, operands: Vec<NumpyOperand>) -> NumpyDType
    requires 0 <= i && i < operands.len(),
    decreases operands.len() - i
{
    if i + 1 == operands.len() {
        operand_type(operands[i as usize])
    } else {
        promote_types(operand_type(operands[i as usize]), max_type_from(i+1, operands))
    }
}

spec fn max_operand_type(operands: Vec<NumpyOperand>) -> NumpyDType
    requires operands.len() > 0
{
    max_type_from(0, operands)
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
    /* code modified by LLM (iteration 5): compute result using spec helper max_operand_type */
    max_operand_type(operands)
}
// </vc-code>

}
fn main() {}