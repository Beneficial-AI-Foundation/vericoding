/* This problem involves determining the index of the first occurrence of a specified element within an array of integers. The objective is to identify the correct position where the target element appears for the first time, ensuring that all elements prior to that index are different from the target.

-----Input-----
The input consists of:
• a: An array of integers.
• e: An integer representing the element to search for.

-----Output-----
The output is a natural number (usize) representing the index of the first occurrence of e in the array.
• If the element e exists in the array, the index n will satisfy the conditions specified above.

-----Note-----
It is assumed that the input satisfies the precondition where at least one index i in a exists such that a[i] = e.
The implementation uses a helper function to iterate through the array recursively. */

use vstd::prelude::*;

verus! {
fn linear_search_aux(a: &Vec<i32>, e: i32, n: usize) -> (result: usize)
    requires n <= a.len(),
    decreases a.len() - n,
{
    if n < a.len() {
        if a[n] == e {
            n
        } else {
            linear_search_aux(a, e, n + 1)
        }
    } else {
        0
    }
}
fn linear_search(a: &Vec<i32>, e: i32) -> (result: usize)
    requires exists|i: int| 0 <= i < a.len() && a[i] == e,
    ensures
        result < a.len(),
        a[result as int] == e,
        forall|k: int| 0 <= k < result ==> a[k] != e,
{
    // impl-start
    assume(false);
    0
    // impl-end
}
}
fn main() {}