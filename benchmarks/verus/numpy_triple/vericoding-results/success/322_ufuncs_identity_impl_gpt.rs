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
/* helper modified by LLM (iteration 2): prove identity element for addition */
proof fn lemma_identity_add()
    ensures
        has_identity(OpType::Add, 0)
{
    assert forall|x: int| apply_op(OpType::Add, x, 0int) == x && apply_op(OpType::Add, 0int, x) == x by {
        assert(apply_op(OpType::Add, x, 0int) == x + 0int);
        assert(x + 0int == x);
        assert(apply_op(OpType::Add, 0int, x) == 0int + x);
        assert(0int + x == x);
    }
}

/* helper modified by LLM (iteration 2): prove identity element for multiplication */
proof fn lemma_identity_multiply()
    ensures
        has_identity(OpType::Multiply, 1)
{
    assert forall|x: int| apply_op(OpType::Multiply, x, 1int) == x && apply_op(OpType::Multiply, 1int, x) == x by {
        assert(apply_op(OpType::Multiply, x, 1int) == x * 1int);
        assert(x * 1int == x);
        assert(apply_op(OpType::Multiply, 1int, x) == 1int * x);
        assert(1int * x == x);
    }
}

/* helper modified by LLM (iteration 2): show no identity for LogicalAnd via counterexample x = 2 */
proof fn lemma_no_identity_logical_and()
    ensures
        forall|id: int| !has_identity(OpType::LogicalAnd, id)
{
    assert forall|id: int| !has_identity(OpType::LogicalAnd, id) by {
        assert(apply_op(OpType::LogicalAnd, 2int, id) == if 2int != 0int && id != 0int { 1int } else { 0int });
        if id != 0int {
            assert(apply_op(OpType::LogicalAnd, 2int, id) == 1int);
            assert(1int != 2int);
        } else {
            assert(apply_op(OpType::LogicalAnd, 2int, id) == 0int);
            assert(0int != 2int);
        }
        assert(apply_op(OpType::LogicalAnd, 2int, id) != 2int);
    }
}

/* helper modified by LLM (iteration 2): show no identity for LogicalOr via counterexample x = 2 */
proof fn lemma_no_identity_logical_or()
    ensures
        forall|id: int| !has_identity(OpType::LogicalOr, id)
{
    assert forall|id: int| !has_identity(OpType::LogicalOr, id) by {
        assert(2int != 0int);
        assert(apply_op(OpType::LogicalOr, 2int, id) == if 2int != 0int || id != 0int { 1int } else { 0int });
        assert(apply_op(OpType::LogicalOr, 2int, id) == 1int);
        assert(1int != 2int);
        assert(apply_op(OpType::LogicalOr, 2int, id) != 2int);
    }
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
    /* code modified by LLM (iteration 2): return identities for Add/Multiply; None for logical ops using lemmas */
    match op {
        OpType::Add => {
            proof { lemma_identity_add(); }
            Some(0i8)
        }
        OpType::Multiply => {
            proof { lemma_identity_multiply(); }
            Some(1i8)
        }
        OpType::LogicalAnd => {
            proof { lemma_no_identity_logical_and(); }
            None
        }
        OpType::LogicalOr => {
            proof { lemma_no_identity_logical_or(); }
            None
        }
    }
}
// </vc-code>


}
fn main() {}