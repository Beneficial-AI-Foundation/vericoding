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
/* helper modified by LLM (iteration 5): Add decreases clause to recursive lemma */
proof fn lemma_count_ones_in_column(a: Seq<int>, n: int, k: int, col: int, j: int)
    requires
        0 <= col < k,
        valid_input(n, k, a),
        j >= 0
    ensures
        count_ones_in_column(a, n, k, col) == (
            if j < n {
                (if j % k == col && a[j] == 1 { 1int } else { 0int }) + 
                count_ones_in_column(a, n, k, col)
            } else {
                count_ones_in_column(a, n, k, col)
            }
        ),
        count_twos_in_column(a, n, k, col) == (
            if j < n {
                (if j % k == col && a[j] == 2 { 1int } else { 0int }) + 
                count_twos_in_column(a, n, k, col)
            } else {
                count_twos_in_column(a, n, k, col)
            }
        )
    decreases n - j when j <= n
{
    if j < n {
        lemma_count_ones_in_column(a, n, k, col, j + 1);
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
    /* code modified by LLM (iteration 5): Fix loop invariant for j % k_i condition */
    let mut total_changes: i8 = 0;
    let n_i = n as usize;
    let k_i = k as usize;
    let mut col: usize = 0;
    
    while col < k_i
        invariant
            0 <= col as int <= k as int,
            total_changes as int == sum_min_changes_helper(a@.map(|i, v| v as int), n as int, k as int, col as int),
            0 <= total_changes as int <= n as int
        decreases k_i - col
    {
        let mut count1: i8 = 0;
        let mut count2: i8 = 0;
        let mut j: usize = col;
        
        while j < n_i
            invariant
                j <= n_i,
                count1 as int == count_ones_in_column(a@.map(|i, v| v as int), n as int, k as int, col as int),
                count2 as int == count_twos_in_column(a@.map(|i, v| v as int), n as int, k as int, col as int),
                0 <= count1 as int <= (n_i / k_i) as int,
                0 <= count2 as int <= (n_i / k_i) as int
            decreases n_i - j
        {
            if a[j] == 1 {
                count1 += 1;
            } else if a[j] == 2 {
                count2 += 1;
            }
            j += k_i;
        }
        
        let min_changes = if count1 < count2 { count1 } else { count2 };
        total_changes += min_changes;
        col += 1;
    }
    
    total_changes
}
// </vc-code>


}

fn main() {}