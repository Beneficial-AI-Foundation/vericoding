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
fn count_column(a: &Vec<i8>, n: i8, k: i8, col: i8) -> (i8, i8)
    requires
        valid_input(n as int, k as int, a@.map(|i, v| v as int)),
        0 <= col < k
    ensures
        let (ones, twos) = result;
        ones as int == count_ones_in_column(a@.map(|i, v| v as int), n as int, k as int, col as int),
        twos as int == count_twos_in_column(a@.map(|i, v| v as int), n as int, k as int, col as int)
/* helper modified by LLM (iteration 5): fixed ensures clause to use result pattern instead of recursive call */
{
    let mut ones: i8 = 0;
    let mut twos: i8 = 0;
    let mut j = col;
    while j < n
        invariant
            col <= j <= n,
            ones as int == Set::new(|i: int| (col as int) <= i < (j as int) && i % (k as int) == (col as int) && a@[i as usize] as int == 1).len(),
            twos as int == Set::new(|i: int| (col as int) <= i < (j as int) && i % (k as int) == (col as int) && a@[i as usize] as int == 2).len(),
        decreases (n - j) as int
    {
        let value = a[j as usize];
        if value == 1 {
            ones += 1;
        } else {
            twos += 1;
        }
        j += k;
    }
    (ones, twos)
}
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
/* code modified by LLM (iteration 5): no changes required */
    let mut total: i8 = 0;
    let mut col = 0;
    while col < k
        invariant
            0 <= col <= k,
            total as int + sum_min_changes_helper(a@.map(|i, v| v as int), n as int, k as int, col as int) == sum_min_changes_helper(a@.map(|i, v| v as int), n as int, k as int, 0),
        decreases (k - col) as int
    {
        let (ones, twos) = count_column(&a, n, k, col);
        let min_in_col = if ones < twos { ones } else { twos };
        total += min_in_col;
        col += 1;
    }
    total
}
// </vc-code>


}

fn main() {}