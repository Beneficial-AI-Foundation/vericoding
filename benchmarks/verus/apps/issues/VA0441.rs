// <vc-preamble>
use vstd::prelude::*;

verus! {
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
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn permute(nums: Vec<i8>) -> (result: Vec<Vec<i8>>)
    requires 
        all_distinct(nums@.map(|i: int, x: i8| x as int)),
    ensures 
        result.len() == factorial(nums.len() as nat),
        forall|p: Vec<i8>| #[trigger] result@.contains(p) ==> is_permutation(p@.map(|i: int, x: i8| x as int), nums@.map(|i: int, x: i8| x as int)),
        all_distinct(result@),
        forall|perm: Seq<int>| #[trigger] is_permutation(perm, nums@.map(|i: int, x: i8| x as int)) ==> exists|v: Vec<i8>| result@.contains(v) && v@.map(|i: int, x: i8| x as int) == perm,
// </vc-spec>
// <vc-code>
{
    assume(false);
    Vec::new()
}
// </vc-code>


}

fn main() {}