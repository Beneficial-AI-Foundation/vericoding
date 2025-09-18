// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): provide witness_exists lemma as spec function proving existence at index idx */
fn witness_exists(a: &Vec<i32>, idx: int)
    requires
        0 <= idx,
        idx + 1 < a.len(),
    ensures
        exists|k: int| { 0 <= k < idx + 1, a[k] + 1 == a[(k + 1) as int] },
{
    proof {
        exists(idx);
        assert(0 <= idx && idx < idx + 1);
        assert(a[idx] + 1 == a[(idx + 1) as int]);
    }
}
// </vc-helpers>

// <vc-spec>
fn contains_consecutive_numbers(a: &Vec<i32>) -> (result: bool)
    ensures
        result <==> exists|i: int| {
            &&& 0 <= i < a.len() - 1
            &&& #[trigger] a[i] + 1 == a[(i + 1) as int]
        },
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): iterate to detect consecutive pair and maintain invariant using witness_exists */
{
    if a.len() < 2 {
        return false;
    }
    let mut i: int = 0;
    let mut found: bool = false;
    while i < a.len() - 1
        invariant
            0 <= i <= a.len() - 1,
            found <==> exists|k: int| { 0 <= k < i && a[k] + 1 == a[(k + 1) as int] },
        decreases a.len() - i
    {
        if a[i] + 1 == a[(i + 1) as int] {
            found = true;
        }
        let old_i: int = i;
        i = i + 1;
        proof {
            if found {
                witness_exists(a, old_i);
            }
        }
    }
    found
}
// </vc-code>

}
fn main() {}