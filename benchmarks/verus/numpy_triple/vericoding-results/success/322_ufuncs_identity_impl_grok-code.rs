// <vc-preamble>
use vstd::prelude::*;

verus! {
enum OpType {
    Add,
    Multiply,
    LogicalAnd,
    LogicalOr,
}

spec fn apply_op(op: OpType, x: int, y: int) -> int {
    match op {
        OpType::Add => x + y,
        OpType::Multiply => x * y,
        OpType::LogicalAnd => if x != 0 && y != 0 { 1 } else { 0 },
        OpType::LogicalOr => if x != 0 || y != 0 { 1 } else { 0 },
    }
}

spec fn has_identity(op: OpType, id: int) -> bool {
    forall|x: int| apply_op(op, x, id) == x && apply_op(op, id, x) == x
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_add_identity()
    ensures
        has_identity(OpType::Add, 0)
{
    assert forall |x: int| #[trigger] apply_op(OpType::Add, x, 0) == x by { };
}

proof fn lemma_multiply_identity()
    ensures
        has_identity(OpType::Multiply, 1)
{
    assert forall |x: int| #[trigger] apply_op(OpType::Multiply, x, 1) == x by { };
}

proof fn lemma_no_identity_logical_and()
    ensures
        forall |id: int| !has_identity(OpType::LogicalAnd, id)
{
    assert forall |id: int| !has_identity(OpType::LogicalAnd, id) by {
        let x = 2;
        assert(apply_op(OpType::LogicalAnd, x, id) != x);
    };
}

proof fn lemma_no_identity_logical_or()
    ensures
        forall |id: int| !has_identity(OpType::LogicalOr, id)
{
    assert forall |id: int| !has_identity(OpType::LogicalOr, id) by {
        let x = 2;
        assert(apply_op(OpType::LogicalOr, x, id) != x);
    };
}
// </vc-helpers>

// <vc-spec>
fn ufunc_identity(op: OpType) -> (result: Option<i8>)
    ensures
        match result {
            Some(id) => has_identity(op, id as int),
            None => forall|id: int| !has_identity(op, id)
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): added proof calls to lemmas to prove the postcondition */
{
    match op {
        OpType::Add => {
            let id: i8 = 0;
            proof { lemma_add_identity(); }
            Some(id)
        },
        OpType::Multiply => {
            let id: i8 = 1;
            proof { lemma_multiply_identity(); }
            Some(id)
        },
        OpType::LogicalAnd => {
            proof { lemma_no_identity_logical_and(); }
            None
        },
        OpType::LogicalOr => {
            proof { lemma_no_identity_logical_or(); }
            None
        },
    }
}
// </vc-code>


}
fn main() {}