// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_permut(a: Seq<int>, b: Seq<int>) -> bool
    recommends a.len() == b.len()
{
    a.to_multiset() == b.to_multiset()
}

spec fn sorted(a: Seq<int>) -> bool
{
    forall|i: int, j: int| 0 <= i <= j < a.len() ==> a[i] <= a[j]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed unresolved function call and added an assertion. */
proof fn lemma_swap_maintains_permut(s: Seq<int>, i: int, j: int)
    requires
        0 <= i < s.len(),
        0 <= j < s.len(),
    ensures
        valid_permut(s.update(i, s[j]).update(j, s[i]), s),
{
    assert(s.update(i, s[j]).update(j, s[i]) == s.swap(i, j));
    lemma_swap_preserves_multiset(s, i, j);
}
// </vc-helpers>

// <vc-spec>
fn swap(a: &mut Vec<int>, i: usize, j: usize)
    requires 
        i < old(a).len(),
        j < old(a).len(),
    ensures 
        a.len() == old(a).len(),
        a@ == old(a)@.update(i as int, old(a)@[j as int]).update(j as int, old(a)@[i as int]),
        valid_permut(a@, old(a)@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): No change needed; previous code correct. */
    a.swap(i, j);
    proof {
        lemma_swap_maintains_permut(old(a)@, i as int, j as int);
    }
}
// </vc-code>

}
fn main() {}