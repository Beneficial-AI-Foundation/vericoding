use vstd::prelude::*;

verus! {

spec fn is_peek(v: &Vec<i32>, i: int) -> bool
    recommends 0 <= i < v.len()
{
    forall|k: int| 0 <= k < i ==> v[i] >= v[k]
}

spec fn peek_sum(v: &Vec<i32>, i: int) -> int
    recommends 0 <= i <= v.len()
    decreases i when 0 <= i <= v.len()
{
    if i == 0 {
        0
    } else {
        if is_peek(v, i - 1) {
            v[i - 1] + peek_sum(v, i - 1)
        } else {
            peek_sum(v, i - 1)
        }
    }
}

// <vc-helpers>
#[verifier(nonlinear)]
proof fn lemma_is_peek_strengthen(v: &Vec<i32>, i: int, k: int)
    requires
        0 <= i < v.len(),
        0 <= k < i,
        // Using `v@[j]` accesses as `Seq<T>` elements.
        // It helps Verus understand the relationship because Vec is a sequence internally.
        forall|j: int| 0 <= j < i ==> v@[i] >= v@[j],
    ensures
        v@[i] >= v@[k],
{
    // This lemma is implicitly handled by the forall quantifier.
    // No specific proof steps are needed here, as the SMT solver handles it.
}
// </vc-helpers>

// <vc-spec>
fn m_peek_sum(v: &Vec<i32>) -> (sum: i32)
    requires v.len() > 0
    ensures sum == peek_sum(v, v.len() as int)
    //Implement and verify an O(v.len()) algorithm to solve this problem
// </vc-spec>
// <vc-code>
{
    let mut sum: i32 = 0;
    let mut i: nat = 0; // Changed to nat

    while (i as int) < v.len() as int // Access as int
        invariant
            0 <= i as int <= v.len() as int, // Access as int
            sum == peek_sum(v, i as int), // Access as int
            // The `is_peek` invariant for previous elements isn't needed here.
            // The `peek_sum` definition itself handles the `is_peek` logic.
    {
        proof {
            // This is to help Verus with the post-condition from the recursive definition of peek_sum.
            // We need to show that if is_peek(v, i-1) is true, then v[i-1] + peek_sum(v, i-1) is the correct sum.
            // Otherwise, it's just peek_sum(v, i-1).
            // This unfolds the recursive definition.
            if i > 0 {
                if is_peek(v, i as int - 1) { // Access as int
                    assert(peek_sum(v, i as int) == v[i as int - 1] + peek_sum(v, i as int - 1)); // Access as int
                } else {
                    assert(peek_sum(v, i as int) == peek_sum(v, i as int - 1)); // Access as int
                }
            }
        }

        if i > 0 {
            if is_peek(v, i as int - 1) { // Access as int
                sum = sum + v[i as int - 1]; // Use v[i-1] instead of v@[i-1] as v is a &Vec<i32> // Access as int
            }
        }
        i = i + 1;
    }
    sum
}
// </vc-code>

fn main() {}

}