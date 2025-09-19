// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_sorted(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

spec fn multiset_equiv(s1: Seq<i32>, s2: Seq<i32>) -> bool {
    s1.to_multiset() == s2.to_multiset()
}
// </vc-preamble>

// <vc-helpers>
fn merge_sorted_aux(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<i32>)
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
// </vc-helpers>

// <vc-spec>
fn merge_sorted(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<i32>)
    requires 
        is_sorted(a@),
        is_sorted(b@),
    ensures 
        is_sorted(result@),
        multiset_equiv(result@, a@ + b@),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
// </vc-code>

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