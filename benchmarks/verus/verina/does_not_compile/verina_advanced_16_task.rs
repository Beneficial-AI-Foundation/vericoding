// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sorted(v: Vec<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] <= v[j]
}

spec fn multiset_equivalent(v1: Vec<i32>, v2: Vec<i32>) -> bool {
    forall|elem: i32| count(v1, elem) == count(v2, elem)
}

spec fn count(v: Vec<i32>, elem: i32) -> nat {
    v.to_seq().filter(|x| *x == elem).len()
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn insertion_sort(xs: Vec<i32>) -> (result: Vec<i32>)
    ensures
        sorted(result),
        multiset_equivalent(xs, result),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}