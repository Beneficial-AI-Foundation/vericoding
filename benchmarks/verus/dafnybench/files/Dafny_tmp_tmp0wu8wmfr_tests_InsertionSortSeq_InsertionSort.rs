// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_sorted(s: Seq<int>) -> bool {
    forall|p: int, q: int| 0 <= p < q < s.len() ==> s[p] <= s[q]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn insertion_sort(s: Vec<i8>) -> (r: Vec<i8>)
    ensures
        s@.map(|i, x: i8| x as int).to_multiset() == r@.map(|i, x: i8| x as int).to_multiset(),
        is_sorted(r@.map(|i, x: i8| x as int)),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}