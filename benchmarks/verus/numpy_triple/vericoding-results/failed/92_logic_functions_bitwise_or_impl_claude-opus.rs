// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
spec fn bitwise_or(x: i32, y: i32) -> i32;

proof fn bitwise_or_comm(x: i32, y: i32)
    ensures bitwise_or(x, y) == bitwise_or(y, x)
{
    assume(false);
}

proof fn bitwise_or_zero(x: i32)
    ensures bitwise_or(x, 0) == x
{
    assume(false);
}

proof fn bitwise_or_idempotent(x: i32)
    ensures bitwise_or(x, x) == x
{
    assume(false);
}

fn numpy_bitwise_or(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<i8>)
    requires x1.len() == x2.len(),
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as i32 == bitwise_or(x1[i] as i32, x2[i] as i32),
        forall|i: int| 0 <= i < result.len() ==> bitwise_or(x1[i] as i32, x2[i] as i32) == bitwise_or(x2[i] as i32, x1[i] as i32),
        forall|i: int| 0 <= i < result.len() ==> bitwise_or(x1[i] as i32, 0) == x1[i] as i32,
        forall|i: int| 0 <= i < result.len() ==> bitwise_or(x1[i] as i32, x1[i] as i32) == x1[i] as i32,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement without assume statements, rely on proof functions */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x1.len()
        invariant
            0 <= i <= x1.len(),
            x1.len() == x2.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] as i32 == bitwise_or(x1@[j] as i32, x2@[j] as i32),
            forall|j: int| 0 <= j < i ==> bitwise_or(x1@[j] as i32, x2@[j] as i32) == bitwise_or(x2@[j] as i32, x1@[j] as i32),
            forall|j: int| 0 <= j < i ==> bitwise_or(x1@[j] as i32, 0) == x1@[j] as i32,
            forall|j: int| 0 <= j < i ==> bitwise_or(x1@[j] as i32, x1@[j] as i32) == x1@[j] as i32,
        decreases x1.len() - i
    {
        let val = (x1[i] | x2[i]) as i8;
        proof {
            bitwise_or_comm(x1@[i as int] as i32, x2@[i as int] as i32);
            bitwise_or_zero(x1@[i as int] as i32);
            bitwise_or_idempotent(x1@[i as int] as i32);
        }
        result.push(val);
        i = i + 1;
    }
    proof {
        assert(result.len() == x1.len());
        assert(forall|j: int| 0 <= j < result.len() ==> bitwise_or(x1@[j] as i32, x2@[j] as i32) == bitwise_or(x2@[j] as i32, x1@[j] as i32));
        assert(forall|j: int| 0 <= j < result.len() ==> bitwise_or(x1@[j] as i32, 0) == x1@[j] as i32);
        assert(forall|j: int| 0 <= j < result.len() ==> bitwise_or(x1@[j] as i32, x1@[j] as i32) == x1@[j] as i32);
    }
    result
}
// </vc-code>

}
fn main() {}