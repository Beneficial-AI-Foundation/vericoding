// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): arithmetic/indexing helper lemmas for bounds reasoning */
proof fn lemma_index_bounds_for_diff(n: usize, i: usize)
    requires
        n >= 2,
        i + 1 < n,
    ensures
        i < n,
        0 <= i as int < n as int,
        0 <= (i + 1) as int < n as int,
{
    assert(i < n) by {
        assert(i + 1 <= n - 1);
        assert(i < n);
    }
}

proof fn lemma_post_index_ok(a_len: usize, res_len: usize, i: int)
    requires
        res_len + 1 == a_len,
        0 <= i < res_len as int,
    ensures
        0 <= i < a_len as int,
        0 <= i + 1 < a_len as int,
{
    assert(0 <= i + 1);
    assert(i + 1 <= res_len as int);
    assert(i + 1 < a_len as int);
}
// </vc-helpers>

// <vc-spec>
fn numpy_diff(a: Vec<i8>) -> (result: Vec<i8>)
    requires a.len() >= 2,
    ensures 
        result.len() == a.len() - 1,
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == a[i + 1] as int - a[i] as int,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement diff with safe indexing and quantified invariant over processed prefix */
    let n: usize = a.len();
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i + 1 < n
        invariant
            result.len() == i,
            (n as int) == a@.len(),
            forall|k: int|
                0 <= k < i as int ==> result@[k] as int == a@[k + 1] as int - a@[k] as int,
        decreases (n - 1 - i) as int
    {
        lemma_index_bounds_for_diff(n, i);
        let ai1: int = a@[i + 1] as int;
        let ai0: int = a@[i] as int;
        // Compute mathematical difference as int, then cast to i8
        let d_i: int = ai1 - ai0;
        let d: i8 = d_i as i8;
        proof {
            // When the cast preserves value, we can relate back to the int difference
            if i8::MIN as int <= d_i && d_i <= i8::MAX as int {
                assert((d_i as i8) as int == d_i);
            }
        }
        result.push(d);
        i = i + 1;
    }
    // Postconditions
    assert(result.len() == n - 1);
    proof {
        // Show indexing into a is well-formed in the post-quantifier
        assert(forall|j: int| 0 <= j < result.len() as int ==> 0 <= j + 1 < n as int) by {
            assert forall|j: int| 0 <= j < result.len() as int implies 0 <= j + 1 < n as int {
                let j = j;
                lemma_post_index_ok(n, result.len(), j);
            }
        }
    }
    result
}
// </vc-code>


}
fn main() {}