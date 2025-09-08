/* This task requires writing a Verus method that takes two sorted (non-decreasing) integer lists and merges them into a single sorted list. The output must preserve order and include all elements from both input lists.

Input:
The input consists of:
a: A list of integers sorted in non-decreasing order.
b: Another list of integers sorted in non-decreasing order.

Output:
The output is a list of integers:
Returns a merged list that contains all elements from both input lists, sorted in non-decreasing order. */

use vstd::prelude::*;

verus! {

spec fn is_sorted(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

spec fn multiset_equiv(s1: Seq<i32>, s2: Seq<i32>) -> bool {
    s1.to_multiset() == s2.to_multiset()
}
fn merge_sorted_aux(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<i32>)
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
fn merge_sorted(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<i32>)
    requires 
        is_sorted(a@),
        is_sorted(b@),
    ensures 
        is_sorted(result@),
        multiset_equiv(result@, a@ + b@),
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {
    /* 
    -- Invalid Inputs
    [
        {
            "input": {
                "a": "[1, 2, 3]",
                "b": "[6, 5, 4]"
            }
        },
        {
            "input": {
                "a": "[3, 2, 1]",
                "b": "[6, 5, 4]"
            }
        }
    ]
    -- Tests
    [
        {
            "input": {
                "a": "[1, 3, 5]",
                "b": "[2, 4, 6]"
            },
            "expected": "[1, 2, 3, 4, 5, 6]",
            "unexpected": [
                "[1, 3, 5]",
                "[2, 4, 6]",
                "[6, 5, 4]"
            ]
        },
        {
            "input": {
                "a": "[1, 2]",
                "b": "[1, 2, 3]"
            },
            "expected": "[1, 1, 2, 2, 3]",
            "unexpected": [
                "[1, 2, 3]"
            ]
        },
        {
            "input": {
                "a": "[]",
                "b": "[4, 5]"
            },
            "expected": "[4, 5]",
            "unexpected": [
                "[]"
            ]
        },
        {
            "input": {
                "a": "[0, 3, 4]",
                "b": "[]"
            },
            "expected": "[0, 3, 4]",
            "unexpected": [
                "[4, 3, 0]"
            ]
        },
        {
            "input": {
                "a": "[1, 4, 6]",
                "b": "[2, 3, 5]"
            },
            "expected": "[1, 2, 3, 4, 5, 6]",
            "unexpected": [
                "[1, 4, 6, 2, 3, 5]"
            ]
        }
    ]
    */
}