use vstd::prelude::*;

verus! {

// ATOM 
spec fn sorted(s: Seq<int>) -> bool {
    forall|k1: int, k2: int| 0 <= k1 <= k2 < s.len() ==> s[k1] <= s[k2]
}

// Ex1

// SPEC 

// Ex1

pub fn copyArr(a: &Vec<int>, l: int, r: int) -> (ret: Vec<int>)
    requires(0 <= l < r <= a.len())
    ensures(ret@ == a@.subrange(l, r))
{
}

// Ex2

// SPEC 

// Ex2

pub fn mergeArr(a: &mut Vec<int>, l: int, m: int, r: int)
    requires(0 <= l < m < r <= old(a).len())
    requires(sorted(old(a)@.subrange(l, m)) && sorted(old(a)@.subrange(m, r)))
    ensures(sorted(a@.subrange(l, r)))
    ensures(a@.subrange(0, l) == old(a)@.subrange(0, l))
    ensures(a@.subrange(r, a.len() as int) == old(a)@.subrange(r, old(a).len() as int))
{
}

// Ex3

//ATOM_PLACEHOLDER_sort

// SPEC 

pub fn sortAux(a: &mut Vec<int>, l: int, r: int)
    requires(0 <= l < r <= old(a).len())
    ensures(sorted(a@.subrange(l, r)))
    ensures(a@.subrange(0, l) == old(a)@.subrange(0, l))
    ensures(a@.subrange(r, a.len() as int) == old(a)@.subrange(r, old(a).len() as int))
{
}

}