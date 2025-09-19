// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn gcd(a: nat, b: nat) -> nat
    decreases a + b
{
    if a == 0 {
        b
    } else if b == 0 {
        a
    } else if a <= b {
        gcd(a, (b - a) as nat)
    } else {
        gcd((a - b) as nat, b)
    }
}

spec fn gcd_list(arr: Seq<nat>) -> nat
    decreases arr.len()
{
    if arr.len() == 0 {
        0
    } else if arr.len() == 1 {
        arr[0]
    } else {
        gcd(arr[0], gcd_list(arr.skip(1)))
    }
}
// </vc-helpers>

// <vc-spec>
fn find_minimum_array_sum(arr: Vec<nat>) -> (result: nat)
    requires 
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> arr[i] > 0,
    ensures 
        result == (arr.len() as nat) * gcd_list(arr@),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {
    // let test1 = vec![1nat];
    // let result1 = find_minimum_array_sum(test1);
    // assert(result1 == 1);
    
    // let test2 = vec![2nat, 4nat, 6nat];
    // let result2 = find_minimum_array_sum(test2);
    // assert(result2 == 6);
    
    // let test3 = vec![3nat, 6nat, 9nat, 12nat];
    // let result3 = find_minimum_array_sum(test3);
    // assert(result3 == 12);
}