use vstd::prelude::*;

verus! {

spec fn odd(n: nat) -> bool { n % 2 == 1 }
spec fn even(n: nat) -> bool { n % 2 == 0 }

fn partitionOddEven(a: &mut Vec<nat>)
    ensures 
        a@.to_multiset() == old(a)@.to_multiset(),
        !(exists|i: int, j: int| 0 <= i < j < a@.len() && even(a@[i]) && odd(a@[j])),
{
    assume(false);
    unreached()
}

}
fn main() {}