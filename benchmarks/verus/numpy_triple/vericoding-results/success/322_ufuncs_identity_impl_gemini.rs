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
/* helper modified by LLM (iteration 2): Made proof explicit with an assert. */
proof fn lemma_add_identity_is_0()
    ensures
        has_identity(OpType::Add, 0),
{
    assert(has_identity(OpType::Add, 0));
}

/* helper modified by LLM (iteration 2): Made proof explicit with an assert. */
proof fn lemma_multiply_identity_is_1()
    ensures
        has_identity(OpType::Multiply, 1),
{
    assert(has_identity(OpType::Multiply, 1));
}

/* helper modified by LLM (iteration 2): Reviewed existing proof by counter-example. */
proof fn lemma_logical_and_has_no_identity()
    ensures
        forall|id: int| !has_identity(OpType::LogicalAnd, id),
{
    assert forall|id: int| !has_identity(OpType::LogicalAnd, id) by {
        if id == 0 {
            assert(apply_op(OpType::LogicalAnd, 1, 0) != 1);
        } else {
            assert(apply_op(OpType::LogicalAnd, 2, id) != 2);
        }
    };
}

/* helper modified by LLM (iteration 2): Reviewed existing proof by counter-example. */
proof fn lemma_logical_or_has_no_identity()
    ensures
        forall|id: int| !has_identity(OpType::LogicalOr, id),
{
    assert forall|id: int| !has_identity(OpType::LogicalOr, id) by {
        if id == 0 {
            assert(apply_op(OpType::LogicalOr, 2, 0) != 2);
        } else {
            assert(apply_op(OpType::LogicalOr, 0, id) != 0);
        }
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
{
    /* code modified by LLM (iteration 2): Used assert-by blocks to call proof lemmas from an exec function, fixing a mode-checking error. */
    match op {
        OpType::Add => {
            assert(has_identity(op, 0)) by {
                lemma_add_identity_is_0();
            };
            Some(0)
        },
        OpType::Multiply => {
            assert(has_identity(op, 1)) by {
                lemma_multiply_identity_is_1();
            };
            Some(1)
        },
        OpType::LogicalAnd => {
            assert(forall|id: int| !has_identity(op, id)) by {
                lemma_logical_and_has_no_identity();
            };
            None
        },
        OpType::LogicalOr => {
            assert(forall|id: int| !has_identity(op, id)) by {
                lemma_logical_or_has_no_identity();
            };
            None
        },
    }
}
// </vc-code>


}
fn main() {}