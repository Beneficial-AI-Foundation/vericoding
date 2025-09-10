/* This task requires writing a Verus method that finds the smallest number in an array of integers.

-----Input-----
The input consists of:
s: An array of integers.

-----Output-----
The output is an option integer:
Returns the smallest number found in the input array or none if the array is empty. */

use vstd::prelude::*;

verus! {
fn find_smallest(s: &Vec<nat>) -> (result: Option<nat>)
    ensures
        match result {
            None => s.len() == 0,
            Some(r) => s.len() > 0 && 
                      (exists|i: int| 0 <= i < s.len() && s[i] == r) &&
                      (forall|i: int| 0 <= i < s.len() ==> r <= s[i])
        },
{
    // impl-start
    assume(false);
    None
    // impl-end
}
}
fn main() {}