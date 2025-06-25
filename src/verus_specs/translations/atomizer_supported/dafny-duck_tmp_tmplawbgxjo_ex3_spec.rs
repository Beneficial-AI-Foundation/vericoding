use vstd::prelude::*;

verus! {

spec fn sortedbad(s: Seq<char>) -> bool {
    // no b's after non-b's
    (forall|i: int, j: int| 0 <= i <= j < s.len() && s[i] == 'b' && s[j] != 'b' ==> i < j) &&
    // only non-d's before d's
    (forall|i: int, j: int| 0 <= i <= j < s.len() && s[i] != 'd' && s[j] == 'd' ==> i < j)
}

pub fn BadSort(a: Seq<char>) -> (b: Seq<char>)
    requires(forall|i: int| 0 <= i < a.len() ==> a[i] == 'a' || a[i] == 'b' || a[i] == 'c' || a[i] == 'd')
    ensures(sortedbad(b))
    ensures(b.to_multiset() == a.to_multiset())
{
}

}