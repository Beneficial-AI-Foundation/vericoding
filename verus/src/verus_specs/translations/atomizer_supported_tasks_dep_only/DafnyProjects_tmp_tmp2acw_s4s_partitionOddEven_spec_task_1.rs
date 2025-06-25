use vstd::prelude::*;

verus! {

pub fn partitionOddEven(a: &mut Vec<nat>)
    requires old(a).len() > 0
    ensures a@.to_multiset() == old(a)@.to_multiset()
    ensures !(exists|i: int, j: int| 0 <= i < j < a.len() && even(a[i]) && odd(a[j]))
{
}

pub open spec fn odd(n: nat) -> bool { n % 2 == 1 }

pub open spec fn even(n: nat) -> bool { n % 2 == 0 }

}