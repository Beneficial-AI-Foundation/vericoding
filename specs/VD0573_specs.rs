// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sortedbad(s: Seq<char>) -> bool {

    (forall|i: int, j: int| 0 <= i <= j < s.len() && s[i] == 'b' && s[j] != 'b' ==> i < j) &&

    (forall|i: int, j: int| 0 <= i <= j < s.len() && s[i] != 'd' && s[j] == 'd' ==> i < j)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn bad_sort(a: Seq<char>) -> (b: Seq<char>)
    requires 
        forall|i: int| 0 <= i < a.len() ==> a[i] == 'b' || a[i] == 'a' || a[i] == 'd',
    ensures 
        sortedbad(b) && b.to_multiset() == a.to_multiset(),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}