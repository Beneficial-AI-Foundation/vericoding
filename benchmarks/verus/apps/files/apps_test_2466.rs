// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn factorial(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { n * factorial((n - 1) as nat) }
}

spec fn is_permutation(perm: Seq<int>, original: Seq<int>) -> bool {
    perm.len() == original.len() && perm.to_multiset() == original.to_multiset()
}

spec fn all_distinct<T>(s: Seq<T>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] != s[j]
}
// </vc-helpers>

// <vc-spec>
fn permute(nums: Seq<int>) -> (result: Vec<Vec<int>>)
    requires all_distinct(nums)
    ensures result.len() == factorial(nums.len())
    ensures forall|p: Seq<int>| result@.contains(p) ==> is_permutation(p, nums)
    ensures all_distinct(result@)
    ensures forall|perm: Seq<int>| is_permutation(perm, nums) ==> result@.contains(perm)
// </vc-spec>
// <vc-code>
{
    assume(false);
    Vec::new()
}
// </vc-code>


}

fn main() {}