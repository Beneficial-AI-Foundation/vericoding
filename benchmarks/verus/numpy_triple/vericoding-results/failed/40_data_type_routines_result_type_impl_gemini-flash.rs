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
/* helper modified by LLM (iteration 5): Corrected error where `result` was not in scope when `max_dtype_in_operands` was called, moved the definition to after where `result` is in scope */
spec fn max_dtype_in_operands(ops: Seq<NumpyOperand>) -> (result: NumpyDType)
    requires ops.len() > 0,
    ensures
        forall|i: int| 0 <= i < ops.len() ==> type_rank(result) >= type_rank(operand_type(ops[i])),
        exists|i: int| 0 <= i < ops.len() && type_rank(result) == type_rank(operand_type(ops[i]))
{
    if ops.len() == 1 {
        operand_type(ops[0])
    } else {
        let first_operand_type = operand_type(ops[0]);
        let rest_max_dtype = max_dtype_in_operands(ops.drop_front(1));
        promote_types(first_operand_type, rest_max_dtype)
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
/* code modified by LLM (iteration 5): Now calls the helper `max_dtype_in_operands` */
{
    max_dtype_in_operands(operands.seq())
}
// </vc-code>

}
fn main() {}