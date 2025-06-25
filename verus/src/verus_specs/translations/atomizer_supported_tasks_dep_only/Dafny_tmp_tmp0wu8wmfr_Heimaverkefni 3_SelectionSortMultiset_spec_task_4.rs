use vstd::prelude::*;

verus! {

pub fn min_of_multiset(m: Multiset<int>) -> (min: int)
    requires(m != Multiset::empty())
    ensures(m.count(min) > 0)
    ensures(forall|z: int| m.count(z) > 0 ==> min <= z)
{
}

pub fn sort(m: Multiset<int>) -> (s: Seq<int>)
    ensures(s.to_multiset() == m)
    ensures(forall|p: int, q: int| 0 <= p < q < s.len() ==> s[p] <= s[q])
{
}

}