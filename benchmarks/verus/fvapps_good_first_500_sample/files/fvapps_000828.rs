// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn gcd(a: nat, b: nat) -> nat 
    decreases b
{
    if b == 0 {
        a
    } else {
        gcd(b, a % b)
    }
}

spec fn subarray_gcd(arr: Seq<nat>, start: int, end: int) -> nat 
    decreases end - start
{
    if start >= end || start < 0 || end > arr.len() {
        0
    } else if start + 1 == end {
        arr[start]
    } else {
        gcd(arr[start], subarray_gcd(arr, start + 1, end))
    }
}

fn find_largest_gcd_subarray(n: usize, arr: Vec<nat>) -> (result: usize)
    requires 
        n > 0,
        arr.len() == n,
        forall|i: int| 0 <= i < n ==> arr[i] > 0
    ensures
        result > 0,
        result <= n
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
    // println!("{}", find_largest_gcd_subarray(4, vec![2, 4, 8, 3]));
    // println!("{}", find_largest_gcd_subarray(5, vec![10, 10, 10, 5, 5]));
    // println!("{}", find_largest_gcd_subarray(3, vec![6, 12, 6]));
}