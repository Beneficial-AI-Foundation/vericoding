use vstd::prelude::*;

verus! {

// ATOM 
spec fn sorted(s: Seq<int>) -> bool {
    forall|k1: int, k2: int| 0 <= k1 <= k2 < s.len() ==> s[k1] <= s[k2]
}

// Ex1

// SPEC 

// Ex1

pub fn copyArr(a: &[int], l: int, r: int) -> (ret: Vec<int>)
    requires(
        0 <= l < r <= a.len()
    )
    ensures(|ret: Vec<int>|
        ret@ == a@.subrange(l as int, r as int)
    )
{
    unimplemented!()
}

// Ex2

// SPEC 

// Ex2

pub fn mergeArr(a: &mut Vec<int>, l: int, m: int, r: int)
    requires(
        0 <= l < m < r <= old(a).len(),
        sorted(old(a)@.subrange(l as int, m as int)) && sorted(old(a)@.subrange(m as int, r as int))
    )
    ensures(
        sorted(a@.subrange(l as int, r as int)),
        a@.subrange(0, l as int) == old(a)@.subrange(0, l as int),
        a@.subrange(r as int, a.len() as int) == old(a)@.subrange(r as int, old(a).len() as int)
    )
{
    unimplemented!()
}

// Ex3

// SPEC 

// Ex3

pub fn sort(a: &mut Vec<int>)
    ensures(
        sorted(a@)
    )
{
    unimplemented!()
}

// SPEC 

pub fn sortAux(a: &mut Vec<int>, l: int, r: int)
    requires(
        0 <= l < r <= old(a).len()
    )
    ensures(
        sorted(a@.subrange(l as int, r as int)),
        a@.subrange(0, l as int) == old(a)@.subrange(0, l as int),
        a@.subrange(r as int, a.len() as int) == old(a)@.subrange(r as int, old(a).len() as int)
    )
{
    unimplemented!()
}

}