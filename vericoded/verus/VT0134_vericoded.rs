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
proof fn lemma_promote_types_rank(t1: NumpyDType, t2: NumpyDType)
    ensures
        type_rank(promote_types(t1, t2)) >= type_rank(t1),
        type_rank(promote_types(t1, t2)) >= type_rank(t2),
        (type_rank(promote_types(t1, t2)) == type_rank(t1)) || (type_rank(promote_types(t1, t2)) == type_rank(t2)),
{
}

/* helper modified by LLM (iteration 5): fixed move out of shared reference by manually cloning */
fn exec_operand_type(operand: &NumpyOperand) -> (result: NumpyDType)
    ensures
        result == operand_type(*operand),
{
    let dtype = match operand {
        NumpyOperand::Scalar(dtype) => dtype,
        NumpyOperand::Array(dtype, _) => dtype,
    };
    match dtype {
        NumpyDType::Bool => NumpyDType::Bool,
        NumpyDType::Int8 => NumpyDType::Int8,
        NumpyDType::Int16 => NumpyDType::Int16,
        NumpyDType::Int32 => NumpyDType::Int32,
        NumpyDType::Int64 => NumpyDType::Int64,
        NumpyDType::Float32 => NumpyDType::Float32,
        NumpyDType::Float64 => NumpyDType::Float64,
        NumpyDType::Complex64 => NumpyDType::Complex64,
        NumpyDType::Complex128 => NumpyDType::Complex128,
    }
}

/* helper modified by LLM (iteration 5): changed signature to take by reference to fix move errors */
fn exec_type_rank(dtype: &NumpyDType) -> (rank: u8)
    ensures
        rank as nat == type_rank(*dtype),
{
    match *dtype {
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

/* helper modified by LLM (iteration 5): pass references to exec_type_rank */
fn exec_promote_types(t1: NumpyDType, t2: NumpyDType) -> (result: NumpyDType)
    ensures
        result == promote_types(t1, t2),
{
    if exec_type_rank(&t1) >= exec_type_rank(&t2) {
        t1
    } else {
        t2
    }
}

// </vc-helpers>

// <vc-spec>
fn result_type(operands: Vec<NumpyOperand>) -> (result: NumpyDType)
    requires operands.len() > 0,
    ensures

        forall|i: int| 0 <= i < operands.len() as int ==> 
            type_rank(result) >= type_rank(operand_type(operands@[i])),

        exists|i: int| 0 <= i < operands.len() as int && 
            type_rank(result) == type_rank(operand_type(operands@[i])),

        forall|i: int, j: int| 0 <= i < operands.len() as int && 0 <= j < operands.len() as int ==>
            type_rank(result) >= type_rank(promote_types(operand_type(operands@[i]), operand_type(operands@[j]))),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed use-after-move error in loop */
    let mut result = exec_operand_type(&operands[0]);
    let mut i: usize = 1;
    while i < operands.len()
        invariant
            1 <= i <= operands.len(),
            forall|k: int| 0 <= k < i as int ==> 
                type_rank(result) >= type_rank(operand_type(operands@[k])),
            exists|k: int| 0 <= k < i as int && 
                type_rank(result) == type_rank(operand_type(operands@[k])),
        decreases operands.len() - i
    {
        let current_op_type = exec_operand_type(&operands[i]);
        let old_result = result;
        result = exec_promote_types(old_result, current_op_type);
        proof {
            lemma_promote_types_rank(old_result, current_op_type);
        }
        i = i + 1;
    }
    
    proof {
        assert forall|i_idx: int, j_idx: int| 0 <= i_idx < operands.len() as int && 0 <= j_idx < operands.len() as int
        implies type_rank(result) >= type_rank(promote_types(operand_type(operands@[i_idx]), operand_type(operands@[j_idx]))) by {
            let op_i_type = operand_type(operands@[i_idx]);
            let op_j_type = operand_type(operands@[j_idx]);
            let promoted_type = promote_types(op_i_type, op_j_type);
            assert(type_rank(result) >= type_rank(op_i_type));
            assert(type_rank(result) >= type_rank(op_j_type));
            
            if type_rank(op_i_type) >= type_rank(op_j_type) {
                assert(promoted_type == op_i_type);
            } else {
                assert(promoted_type == op_j_type);
            }
        };
    }
    
    result
}

// </vc-code>

}
fn main() {}