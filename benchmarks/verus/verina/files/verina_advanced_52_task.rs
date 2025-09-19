// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn min_operations_precond(nums: Seq<nat>, k: nat) -> bool {
    let target_nums = Seq::new(k, |i: int| (i + 1) as nat);
    forall|n: nat| target_nums.contains(n) ==> nums.contains(n)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn min_operations(nums: Seq<nat>, k: nat) -> (result: nat)
    requires min_operations_precond(nums, k),
    ensures ({
        let processed = nums.reverse().take(result as int);
        let target_nums = Seq::new(k as int, |i: int| (i + 1) as nat);
        let collected_all = forall|n: nat| target_nums.contains(n) ==> processed.contains(n);
        let is_minimal = if result > 0 {
            let processed_minus_one = nums.reverse().take((result - 1) as int);
            !forall|n: nat| target_nums.contains(n) ==> processed_minus_one.contains(n)
        } else {
            k == 0
        };
        collected_all && is_minimal
    }),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
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
                "nums": "[5, 6, 7, 8, 9]",
                "k": 3
            }
        }
    ]
    -- Tests
    [
        {
            "input": {
                "nums": "[3, 1, 5, 4, 2]",
                "k": 2
            },
            "expected": 4,
            "unexpected": [
                1,
                2,
                5
            ]
        },
        {
            "input": {
                "nums": "[3, 1, 5, 4, 2]",
                "k": 5
            },
            "expected": 5,
            "unexpected": [
                1,
                2,
                3
            ]
        },
        {
            "input": {
                "nums": "[3, 2, 5, 3, 1]",
                "k": 3
            },
            "expected": 4,
            "unexpected": [
                1,
                2,
                5
            ]
        },
        {
            "input": {
                "nums": "[5, 4, 3, 2, 1]",
                "k": 1
            },
            "expected": 1,
            "unexpected": [
                0,
                2,
                5
            ]
        },
        {
            "input": {
                "nums": "[5, 4, 1, 2, 3]",
                "k": 3
            },
            "expected": 3,
            "unexpected": [
                1,
                4,
                5
            ]
        },
        {
            "input": {
                "nums": "[1, 3, 2, 2, 1]",
                "k": 2
            },
            "expected": 2,
            "unexpected": [
                1,
                3,
                4
            ]
        },
        {
            "input": {
                "nums": "[10, 1, 20, 2]",
                "k": 2
            },
            "expected": 3,
            "unexpected": [
                1,
                2,
                4
            ]
        },
        {
            "input": {
                "nums": "[1, 2, 3]",
                "k": 0
            },
            "expected": 0,
            "unexpected": [
                1,
                2,
                3
            ]
        }
    ]
    */
}