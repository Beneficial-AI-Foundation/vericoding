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
fn min_changes_for_column_exec(a: &Vec<i8>, n: i8, k: i8, col: i8) -> (result: i8)
    requires
        valid_input(n as int, k as int, a@.map(|i, v| v as int)),
        0 <= col as int < k as int
    ensures
        result as int == min_changes_for_column(a@.map(|i, v| v as int), n as int, k as int, col as int)
    decreases n as int
{
    /* helper modified by LLM (iteration 5): added exec version of min_changes_for_column */
    let mut count1: i32 = 0;
    let mut count2: i32 = 0;
    let k_usize = k as usize;
    let col_usize = col as usize;
    let n_usize = n as usize;
    let ghost k_int = k as int;
    let ghost col_int = col as int;
    let ghost n_int = n as int;
    let ghost a_int = a@.map(|i, v| v as int);
    let mut j: usize = 0;
    while j < n_usize
        invariant
            0 <= j <= n_usize,
            count1 == Set::new(|j_int: int| 0 <= j_int < (j as int) && j_int % k_int == col_int && a_int[j_int] == 1).len() as i32,
            count2 == Set::new(|j_int: int| 0 <= j_int < (j as int) && j_int % k_int == col_int && a_int[j_int] == 2).len() as i32
        decreases n_usize - j
    {
        if (j % k_usize) == col_usize {
            proof {
                assert(j < n_usize);
            }
            if a[j] == 1 {
                count1 += 1;
            } else {
                if a[j] == 2 {
                    count2 += 1;
                }
            }
        }
        j += 1;
    }
    let min_c = if count1 < count2 { count1 } else { count2 };
    return min_c as i8;
}

fn sum_min_changes_helper_exec(a: &Vec<i8>, n: i8, k: i8, col: i8) -> (result: i8)
    requires
        valid_input(n as int, k as int, a@.map(|i, v| v as int)),
        0 <= col as int <= k as int
    ensures
        result as int == sum_min_changes_helper(a@.map(|i, v| v as int), n as int, k as int, col as int)
    decreases (k as int - col as int)
{
    /* helper modified by LLM (iteration 5): added exec version of sum_min_changes_helper */
    if col >= k {
        return 0;
    } else {
        let min_c = min_changes_for_column_exec(a, n, k, col);
        let next = sum_min_changes_helper_exec(a, n, k, col + 1);
        return min_c + next as i8;
    }
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
    /* code modified by LLM (iteration 5): implemented recursive call using exec helpers */
    return sum_min_changes_helper_exec(&a, n, k, 0);
}
// </vc-code>


}

fn main() {}