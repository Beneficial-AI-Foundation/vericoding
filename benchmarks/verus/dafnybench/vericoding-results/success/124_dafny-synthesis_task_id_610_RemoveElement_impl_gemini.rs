// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn remove_element(s: &Vec<i32>, k: usize) -> (v: Vec<i32>)
    requires 
        k < s.len(),
    ensures
        v.len() == s.len() - 1,
        forall|i: int| 0 <= i < k ==> v[i] == s[i],
        forall|i: int| k <= i < v.len() ==> v[i] == s[(i + 1) as int],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added precondition to loop invariants */
    let mut v = Vec::new();
    let mut i: usize = 0;

    while i < k
        invariant
            i <= k,
            k < s.len(),
            v.view() == s.view().subrange(0, i as int),
        decreases k - i
    {
        v.push(s[i]);
        i = i + 1;
    }

    i = k + 1;
    while i < s.len()
        invariant
            k < i <= s.len(),
            k < s.len(),
            v.view() == s.view().subrange(0, k as int) + s.view().subrange(k + 1, i as int),
        decreases s.len() - i
    {
        v.push(s[i]);
        i = i + 1;
    }

    v
}
// </vc-code>

}
fn main() {}