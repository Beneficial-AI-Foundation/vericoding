// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn array_index(v: Seq<i32>, i: int) -> i32 {
    v[i]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): This helper is correct but was not being used */
spec fn reversed_prefix(s: Seq<i32>, k: int) -> Seq<i32>
{
    Seq::new(s.len(), |i: int|
        if i < k {
            s[k - 1 - i]
        } else {
            s[i]
        }
    )
}

// </vc-helpers>

// <vc-spec>
fn reverse_upto_k(s: &mut Vec<i32>, k: usize)
    requires 
        2 <= k,
        k <= old(s).len(),
    ensures 
        s.len() == old(s).len(),
        forall|i: int| 0 <= i < k ==> array_index(s@, i) == array_index(old(s)@, k - 1 - i),
        forall|i: int| k <= i < s.len() ==> array_index(s@, i) == array_index(old(s)@, i),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): replaced s.swap with a manual swap to fix a compiler error */
    let mut i: usize = 0;
    while i < k / 2
        invariant
            s.len() == old(s).len(),
            k <= s.len(),
            i <= k / 2,
            forall|l: int| (k as int) <= l < s.len() ==> s@[l] == old(s)@[l],
            forall|l: int| 0 <= l < (i as int) ==> s@[l] == old(s)@[(k as int) - 1 - l],
            forall|l: int| (k as int) - (i as int) <= l < (k as int) ==> s@[l] == old(s)@[(k as int) - 1 - l],
            forall|l: int| (i as int) <= l < (k as int) - (i as int) ==> s@[l] == old(s)@[l],
        decreases k / 2 - i
    {
        let j = k - 1 - i;
        let temp_i = s[i];
        let temp_j = s[j];
        s.set(i, temp_j);
        s.set(j, temp_i);
        i = i + 1;
    }
}

// </vc-code>

}
fn main() {}