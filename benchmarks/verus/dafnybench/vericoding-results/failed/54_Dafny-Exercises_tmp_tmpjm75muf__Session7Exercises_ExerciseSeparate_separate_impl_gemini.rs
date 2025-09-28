// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn strict_negative(v: &Vec<i32>, i: usize, j: usize) -> bool
    recommends 0 <= i <= j <= v.len()
{
    forall|u: usize| i <= u < j ==> v[u as int] < 0
}

spec fn positive(s: Seq<i32>) -> bool {
    forall|u: int| 0 <= u < s.len() ==> s[u] >= 0
}

spec fn is_permutation(s: Seq<i32>, t: Seq<i32>) -> bool {
    s.to_multiset() == t.to_multiset()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): fixed swap postcondition to use `update` for Seq semantics */
fn swap_elements(v: &mut Vec<i32>, i: usize, j: usize)
    requires
        i < v.len(),
        j < v.len(),
    ensures
        v.len() == old(v).len(),
        v@ == old(v)@.update(i as int, old(v)@[j as int]).update(j as int, old(v)@[i as int]),
{
    let temp = v[i];
    v.set(i, v[j]);
    v.set(j, temp);
}
// </vc-helpers>

// <vc-spec>
fn separate(v: &mut Vec<i32>) -> (i: usize)
    ensures
        0 <= i <= v.len(),
        positive(v@.subrange(0, i as int)),
        strict_negative(v, i, v.len()),
        is_permutation(v@, old(v)@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): no change to body; logic is correct with fixed helper */
    let mut left: usize = 0;
    let mut right: usize = v.len();

    while left < right
        invariant
            0 <= left <= right <= v.len(),
            positive(v@.subrange(0, left as int)),
            strict_negative(v, right, v.len()),
            is_permutation(v@, old(v)@),
        decreases right - left
    {
        if v[left] >= 0 {
            left = left + 1;
        } else {
            right = right - 1;
            swap_elements(v, left, right);
        }
    }
    
    left
}
// </vc-code>

}
fn main() {}