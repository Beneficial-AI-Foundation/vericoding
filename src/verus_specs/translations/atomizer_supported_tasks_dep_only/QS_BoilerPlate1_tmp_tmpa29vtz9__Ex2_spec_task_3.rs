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
        ret@ == a@.subrange(l, r)
    )
{
}

// Ex2

// SPEC 

// Ex2

pub fn mergeArr(a: &mut [int], l: int, m: int, r: int)
    requires(
        0 <= l < m < r <= old(a).len() &&
        sorted(old(a)@.subrange(l, m)) && sorted(old(a)@.subrange(m, r))
    )
    ensures(
        sorted(a@.subrange(l, r)) &&
        a@.subrange(0, l) == old(a)@.subrange(0, l) &&
        a@.subrange(r, a.len() as int) == old(a)@.subrange(r, old(a).len() as int)
    )
{
}

// Ex3

// SPEC 

// Ex3

pub fn sort(a: &mut [int])
    ensures(
        sorted(a@)
    )
{
}

// SPEC 

pub fn sortAux(a: &mut [int], l: int, r: int)
    requires(
        0 <= l < r <= old(a).len()
    )
    ensures(
        sorted(a@.subrange(l, r)) &&
        a@.subrange(0, l) == old(a)@.subrange(0, l) &&
        a@.subrange(r, a.len() as int) == old(a)@.subrange(r, old(a).len() as int)
    )
{
}

}