// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): unfold definition of nonzero_helper for any sequence */
proof fn lemma_nonzero_helper_unfold(arr: Seq<f32>)
    ensures
        nonzero_helper(arr) ==
            if arr.len() == 0 {
                0
            } else {
                let rest_count = nonzero_helper(arr.skip(1));
                if arr[0] == 0.0f32 { rest_count } else { rest_count + 1 }
            },
{
}

/* helper modified by LLM (iteration 2): skipping a full-length sequence yields empty */
proof fn lemma_skip_len_is_empty<T>(s: Seq<T>)
    ensures
        s.skip(s.len()).len() == 0,
{
}
// </vc-helpers>

// <vc-spec>
spec fn nonzero_helper(arr: Seq<f32>) -> nat 
    decreases arr.len()
{
    if arr.len() == 0 {
        0
    } else {
        let rest_count = nonzero_helper(arr.skip(1));
        if arr[0] == 0.0f32 {
            rest_count
        } else {
            rest_count + 1
        }
    }
}

fn nonzero(arr: Vec<f32>) -> (result: usize)
    ensures 
        result <= arr.len(),
        result == nonzero_helper(arr@),
        arr.len() > 0 && arr[0] == 0.0f32 ==> 
            nonzero_helper(arr@.skip(1)) == if result > 0 { result - 1 } else { 0 }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): count nonzero entries using a loop with invariants matching the spec */
    let n = arr.len();
    let mut i: usize = 0usize;
    let mut count: usize = 0usize;

    while i < n
        invariant
            i <= n,
            count <= i,
            (count as nat) + nonzero_helper(arr@.skip(i)) == nonzero_helper(arr@),
        decreases n - i
    {
        proof {
            // Facts about the current suffix arr@.skip(i)
            lemma_nonzero_helper_unfold(arr@.skip(i));
            assert(arr@.skip(i).len() == n - i);
            assert(arr@.skip(i).len() > 0);
            assert(arr@.skip(i)[0] == arr@[i]);
            assert(arr@[i] == arr[i]);
            assert(arr@.skip(i).skip(1) == arr@.skip(i + 1));
        }
        if arr[i] != 0.0f32 {
            // Using the unfolding, we know nonzero_helper(arr@.skip(i))
            // equals nonzero_helper(arr@.skip(i+1)) + 1 here
            count = count + 1;
            proof {
                // Help the solver relate helpers across i and i+1 in the nonzero case
                lemma_nonzero_helper_unfold(arr@.skip(i));
                assert(arr@.skip(i).len() == n - i);
                assert(arr@.skip(i).len() > 0);
                assert(arr@.skip(i)[0] == arr[i]);
                assert(arr@.skip(i).skip(1) == arr@.skip(i + 1));
                // Therefore, nonzero_helper(arr@.skip(i)) == nonzero_helper(arr@.skip(i+1)) + 1
            }
        } else {
            // Zero case: helper does not increase
            proof {
                lemma_nonzero_helper_unfold(arr@.skip(i));
                assert(arr@.skip(i).len() == n - i);
                assert(arr@.skip(i).len() > 0);
                assert(arr@.skip(i)[0] == arr[i]);
                assert(arr@.skip(i).skip(1) == arr@.skip(i + 1));
                // Therefore, nonzero_helper(arr@.skip(i)) == nonzero_helper(arr@.skip(i+1))
            }
        }
        i = i + 1;
    }

    proof {
        // At loop exit, i == n
        assert(i == n);
        // Show that the remaining suffix has zero nonzeros
        lemma_skip_len_is_empty(arr@);
        lemma_nonzero_helper_unfold(arr@.skip(n));
        assert(arr@.skip(n).len() == 0);
    }

    count
}
// </vc-code>


}
fn main() {}