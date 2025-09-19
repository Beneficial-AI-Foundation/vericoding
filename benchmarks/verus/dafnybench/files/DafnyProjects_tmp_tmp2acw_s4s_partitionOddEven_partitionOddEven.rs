// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn odd(n: nat) -> bool { n % 2 == 1 }
spec fn even(n: nat) -> bool { n % 2 == 0 }
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn partitionOddEven(a: &mut Vec<u8>)
    ensures 
        a@.map_values(|x: u8| x as nat).to_multiset() == old(a)@.map_values(|x: u8| x as nat).to_multiset(),
        !(exists|i: int, j: int| 0 <= i < j < a@.len() && even(a@[i] as nat) && odd(a@[j] as nat)),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}