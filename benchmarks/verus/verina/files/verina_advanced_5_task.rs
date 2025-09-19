// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

spec fn list_to_nat(l: Seq<u32>) -> nat
    decreases l.len(),
{
    if l.len() == 0 {
        0nat
    } else {
        l[0] as nat + 10nat * list_to_nat(l.subrange(1, l.len() as int))
    }
}
// </vc-helpers>

// <vc-spec>
fn add_two_numbers(l1: &Vec<u32>, l2: &Vec<u32>) -> (result: Vec<u32>)
    requires 
        l1.len() > 0,
        l2.len() > 0,
        forall|i: int| 0 <= i < l1.len() ==> l1[i] < 10,
        forall|i: int| 0 <= i < l2.len() ==> l2[i] < 10,
        (l1[l1.len() - 1] != 0 || l1@ == seq![0u32]) &&
        (l2[l2.len() - 1] != 0 || l2@ == seq![0u32]),
    ensures
        list_to_nat(result@) == list_to_nat(l1@) + list_to_nat(l2@),
        forall|i: int| 0 <= i < result.len() ==> result[i] < 10,
        result[result.len() - 1] != 0 || (l1@ == seq![0u32] && l2@ == seq![0u32] && result@ == seq![0u32]),
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
                "l1": "[]",
                "l2": "[]"
            }
        },
        {
            "input": {
                "l1": "[0, 0]",
                "l2": "[0, 0]"
            }
        }
    ]
    -- Tests
    [
        {
            "input": {
                "l1": "[2,4,3]",
                "l2": "[5,6,4]"
            },
            "expected": "[7,0,8]",
            "unexpected": [
                "[2,4,3]",
                "[0]"
            ]
        },
        {
            "input": {
                "l1": "[0]",
                "l2": "[0]"
            },
            "expected": "[0]",
            "unexpected": [
                "[0,0]"
            ]
        },
        {
            "input": {
                "l1": "[9,9,9,9,9,9,9]",
                "l2": "[9,9,9,9]"
            },
            "expected": "[8,9,9,9,0,0,0,1]",
            "unexpected": [
                "[9,9,9,9,9,9,9,9]"
            ]
        },
        {
            "input": {
                "l1": "[1,2,3]",
                "l2": "[4,5]"
            },
            "expected": "[5,7,3]",
            "unexpected": [
                "[5,7]",
                "[5,7,4]"
            ]
        }
    ]
    */
}