use vstd::prelude::*;

verus! {

pub fn MinOfMultiset(m: Multiset<int>) -> (min: int)
    requires(m != Multiset::empty())
    ensures(m.count(min) > 0)
    ensures(forall|z: int| m.count(z) > 0 ==> min <= z)
{
}

pub fn Main()
{
}

pub fn Sort(m: Multiset<int>) -> (s: Seq<int>)
    ensures(s.to_multiset() == m)
    ensures(forall|p: int, q: int| 0 <= p < q < s.len() ==> s[p] <= s[q])
{
}

}