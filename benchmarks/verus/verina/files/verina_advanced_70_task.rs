/* This task requires writing a Verus method that's goal is to determine the minimum number of adjacent swaps needed to make the array semi-ordered. You may repeatedly swap 2 adjacent elements in the array. A permutation is called semi-ordered if the first number equals 1 and the last number equals n.

Input:

The input consists of:
- nums: A vector of integers.

Output:

The output is an integer. */

use vstd::prelude::*;

verus! {
fn semi_ordered_permutation(nums: &Vec<i32>) -> (result: i32)
    ensures 
        result >= 0
{
    // impl-start
    assume(false);
    0
    // impl-end
}
}
fn main() {}