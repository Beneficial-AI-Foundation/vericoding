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
    /* code modified by LLM (iteration 4): Fixed type mismatch in modulo operation */
    let mut total_changes: i8 = 0;
    let mut col: i8 = 0;
    
    while col < k
        invariant
            0 <= col <= k,
            0 <= total_changes <= n,
            total_changes as int == sum_min_changes_helper(a@.map(|i, v| v as int), n as int, k as int, 0) - sum_min_changes_helper(a@.map(|i, v| v as int), n as int, k as int, col as int)
        decreases k - col
    {
        let mut count1: i8 = 0;
        let mut count2: i8 = 0;
        let mut j: i8 = col;
        
        while j < n
            invariant
                0 <= col < k,
                col <= j,
                j <= n,
                (j as int - col as int) % (k as int) == 0,
                0 <= count1 <= n,
                0 <= count2 <= n,
                count1 as int == Set::new(|idx: int| 0 <= idx < j as int && idx % (k as int) == (col as int) && a@.map(|i, v| v as int)[idx] == 1).len() as int,
                count2 as int == Set::new(|idx: int| 0 <= idx < j as int && idx % (k as int) == (col as int) && a@.map(|i, v| v as int)[idx] == 2).len() as int
            decreases n - j
        {
            if j < n && j >= 0 {
                if a[j as usize] == 1 {
                    if count1 < n {
                        count1 = count1 + 1;
                    }
                } else {
                    if count2 < n {
                        count2 = count2 + 1;
                    }
                }
            }
            if j + k <= n {
                j = j + k;
            } else {
                j = n;
            }
        }
        
        let min_changes = if count1 < count2 { count1 } else { count2 };
        if total_changes + min_changes <= n {
            total_changes = total_changes + min_changes;
        }
        col = col + 1;
    }
    
    total_changes
}
// </vc-code>


}

fn main() {}