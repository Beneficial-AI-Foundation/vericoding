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
/* helper modified by LLM (iteration 5): fixed int casting to use proof blocks for ghost code */
fn lemma_count_ones_twos_sum(a: Seq<int>, n: int, k: int, col: int)
    requires
        1 <= k <= n <= 100,
        n % k == 0,
        a.len() == n,
        0 <= col < k,
        forall|i: int| 0 <= i < a.len() ==> a[i] == 1 || a[i] == 2
    ensures
        count_ones_in_column(a, n, k, col) + count_twos_in_column(a, n, k, col) == n / k
{
    let rows = n / k;
    let ones_set = Set::new(|j: int| 0 <= j < n && j % k == col && a[j] == 1);
    let twos_set = Set::new(|j: int| 0 <= j < n && j % k == col && a[j] == 2);
    let all_set = Set::new(|j: int| 0 <= j < n && j % k == col);
    
    assert(ones_set.union(twos_set) =~= all_set);
    assert(ones_set.intersect(twos_set) =~= Set::empty());
    assert(all_set.len() == rows);
}

fn lemma_sum_min_changes_bound(a: Seq<int>, n: int, k: int)
    requires
        1 <= k <= n <= 100,
        n % k == 0,
        a.len() == n,
        forall|i: int| 0 <= i < a.len() ==> a[i] == 1 || a[i] == 2
    ensures
        0 <= sum_min_changes_for_all_columns(a, n, k) <= n
{
    proof {
        lemma_sum_min_changes_helper_bound(a, n, k, 0);
    }
}

fn lemma_sum_min_changes_helper_bound(a: Seq<int>, n: int, k: int, col: int)
    requires
        1 <= k <= n <= 100,
        n % k == 0,
        a.len() == n,
        0 <= col <= k,
        forall|i: int| 0 <= i < a.len() ==> a[i] == 1 || a[i] == 2
    ensures
        0 <= sum_min_changes_helper(a, n, k, col) <= (k - col) * (n / k)
    decreases k - col
{
    if col >= k {
        // base case
    } else {
        lemma_count_ones_twos_sum(a, n, k, col);
        proof {
            lemma_sum_min_changes_helper_bound(a, n, k, col + 1);
        }
        let min_col = min_changes_for_column(a, n, k, col);
        let count1 = count_ones_in_column(a, n, k, col);
        let count2 = count_twos_in_column(a, n, k, col);
        assert(min_col <= count1 && min_col <= count2);
        assert(count1 + count2 == n / k);
        assert(min_col <= n / k / 2);
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
    /* code modified by LLM (iteration 5): fixed int casting to use proof blocks for ghost code */
    let mut total_changes: i8 = 0;
    let mut col: i8 = 0;
    
    while col < k
        invariant
            0 <= col <= k,
            0 <= total_changes <= col * (n / k),
            total_changes as int == sum_min_changes_helper(a@.map(|i, v| v as int), n as int, k as int, col as int)
        decreases k - col
    {
        let mut count_ones: i8 = 0;
        let mut count_twos: i8 = 0;
        let mut row: i8 = 0;
        
        while row < n / k
            invariant
                0 <= row <= n / k,
                0 <= count_ones <= row,
                0 <= count_twos <= row,
                count_ones + count_twos == row
            decreases n / k - row
        {
            let idx = row * k + col;
            if a[idx as usize] == 1 {
                count_ones = count_ones + 1;
            } else {
                count_twos = count_twos + 1;
            }
            row = row + 1;
        }
        
        let min_changes = if count_ones < count_twos { count_ones } else { count_twos };
        total_changes = total_changes + min_changes;
        
        proof {
            lemma_count_ones_twos_sum(a@.map(|i, v| v as int), n as int, k as int, col as int);
        }
        
        col = col + 1;
    }
    
    proof {
        lemma_sum_min_changes_bound(a@.map(|i, v| v as int), n as int, k as int);
    }
    
    total_changes
}
// </vc-code>


}

fn main() {}