use vstd::prelude::*;

verus! {

// Rearranges the elements in an array 'a' of natural numbers,
// so that all odd numbers appear before all even numbers.
// SPEC 
// Rearranges the elements in an array 'a' of natural numbers,
// so that all odd numbers appear before all even numbers.
pub fn partitionOddEven(a: &mut Vec<nat>)
    requires(old(a).len() == a.len())
    ensures(a@.to_multiset() == old(a)@.to_multiset())
    ensures(!(exists|i: int, j: int| 0 <= i < j < a.len() && even(a[i]) && odd(a[j])))
{
}

// ATOM 
pub open spec fn odd(n: nat) -> bool { n % 2 == 1 }

// ATOM 
pub open spec fn even(n: nat) -> bool { n % 2 == 0 }

// SPEC 
pub fn testPartitionOddEven() {
}

}