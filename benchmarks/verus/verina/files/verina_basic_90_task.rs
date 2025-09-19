// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn slope_search_precond(a: &Vec<Vec<i32>>, key: i32) -> bool {
    a.len() > 0 &&
    (forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i].len() == a[0].len()) &&
    (forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a[i].len() - 1 ==> #[trigger] a[i][j] <= a[i][j + 1]) &&
    (forall|j: int, i: int| 0 <= j < a[0].len() && 0 <= i < a.len() - 1 ==> #[trigger] a[i][j] <= a[i + 1][j])
}
// </vc-preamble>

// <vc-helpers>
spec fn get2d(a: &Vec<Vec<i32>>, i: i32, j: i32) -> i32 {
    a[i as int][j as int]
}
// </vc-helpers>

// <vc-spec>
fn slope_search(a: &Vec<Vec<i32>>, key: i32) -> (result: (i32, i32))
    requires slope_search_precond(a, key),
    ensures
        ({
            let (m, n) = result;
            ((m >= 0 && m < a.len() && n >= 0 && n < a[0].len() && a[m as int][n as int] == key) ||
             (m == -1 && n == -1 && forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a[i].len() ==> #[trigger] a[i][j] != key))
        })
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    (-1, -1)
    // impl-end
}
// </vc-code>

}
fn main() {
    /* Invalid Inputs
    [
        {
            "input": {
                "a": "vec![vec![1, 3, 2], vec![0, 6, 5], vec![7, 8, 9]]",
                "key": 2
            }
        }
    ]
    Tests
    [
        {
            "input": {
                "a": "vec![vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 9]]",
                "key": 5
            },
            "expected": "(1, 1)",
            "unexpected": [
                "(1, 2)",
                "(0, 1)"
            ]
        },
        {
            "input": {
                "a": "vec![vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 9]]",
                "key": 3
            },
            "expected": "(0, 2)",
            "unexpected": [
                "(0, 1)",
                "(1, 2)"
            ]
        },
        {
            "input": {
                "a": "vec![vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 9]]",
                "key": 10
            },
            "expected": "(-1, -1)",
            "unexpected": [
                "(1, 1)",
                "(2, 2)"
            ]
        },
        {
            "input": {
                "a": "vec![vec![1, 2, 3, 4]]",
                "key": 4
            },
            "expected": "(0, 3)",
            "unexpected": [
                "(0, 2)",
                "(1, 3)",
                "(0, 4)"
            ]
        },
        {
            "input": {
                "a": "vec![vec![1], vec![2], vec![3], vec![4]]",
                "key": 3
            },
            "expected": "(2, 0)",
            "unexpected": [
                "(1, 0)",
                "(2, 1)"
            ]
        }
    ] */
}