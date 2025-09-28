// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, k: int, a: Seq<int>) -> bool {
    1 <= k <= n <= 100 &&
    n % k == 0 &&
    a.len() == n &&
    forall|i: int| 0 <= i < a.len() ==> a[i] == 1 || a[i] == 2
}

spec fn count_ones_in_column(a: Seq<int>, n: int, k: int, col: int) -> int {
    Set::new(|j: int| 0 <= j < n && j % k == col && a[j] == 1).len() as int
}

spec fn count_twos_in_column(a: Seq<int>, n: int, k: int, col: int) -> int {
    Set::new(|j: int| 0 <= j < n && j % k == col && a[j] == 2).len() as int
}

spec fn min_changes_for_column(a: Seq<int>, n: int, k: int, col: int) -> int {
    let count1 = count_ones_in_column(a, n, k, col);
    let count2 = count_twos_in_column(a, n, k, col);
    if count1 < count2 { count1 } else { count2 }
}

spec fn sum_min_changes_helper(a: Seq<int>, n: int, k: int, col: int) -> int
    decreases k - col when col <= k
{
    if col >= k {
        0
    } else {
        min_changes_for_column(a, n, k, col) + sum_min_changes_helper(a, n, k, col + 1)
    }
}

spec fn sum_min_changes_for_all_columns(a: Seq<int>, n: int, k: int) -> int {
    sum_min_changes_helper(a, n, k, 0)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8, a: Vec<i8>) -> (result: i8)
    requires 
        valid_input(n as int, k as int, a@.map(|i, v| v as int))
    ensures 
        0 <= result as int <= n as int,
        result as int == sum_min_changes_for_all_columns(a@.map(|i, v| v as int), n as int, k as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation error by casting `a@[j as usize]` to `int` instead of `a@[j]`. */
    let mut total_changes: i8 = 0;
    let mut col_idx: i8 = 0;

    while col_idx < k
        invariant
            0 <= col_idx as int <= k as int,
            sum_min_changes_for_all_columns(a@.map(|i,v| v as int), n as int, k as int) == total_changes as int + sum_min_changes_helper(a@.map(|i,v| v as int), n as int, k as int, col_idx as int),
            0 <= total_changes as int <= n as int,
        decreases (k - col_idx) as int
    {
        let mut ones_in_col: i8 = 0;
        let mut twos_in_col: i8 = 0;
        let mut i: i8 = col_idx;

        while i < n
            invariant
                0 <= i as int <= n as int,
                (i as int) % (k as int) == (col_idx as int) % (k as int),
                ones_in_col as int == Set::new(|j: int| 0 <= j < i as int && j % k as int == col_idx as int && a@[j as usize] as int == 1).len() as int,
                twos_in_col as int == Set::new(|j: int| 0 <= j < i as int && j % k as int == col_idx as int && a@[j as usize] as int == 2).len() as int,
            decreases (n - i) as int
        {
            if a[i as usize] == 1 {
                ones_in_col = (ones_in_col + 1);
            } else {
                twos_in_col = (twos_in_col + 1);
            }
            i = (i + k);
        }

        proof {
            assert(ones_in_col as int == count_ones_in_column(a@.map(|idx, val| val as int), n as int, k as int, col_idx as int));
            assert(twos_in_col as int == count_twos_in_column(a@.map(|idx, val| val as int), n as int, k as int, col_idx as int));
        }

        let changes_for_this_col = if ones_in_col < twos_in_col {
            ones_in_col
        } else {
            twos_in_col
        };
        total_changes = (total_changes + changes_for_this_col);
        col_idx = (col_idx + 1);
    }
    total_changes
}
// </vc-code>


}

fn main() {}