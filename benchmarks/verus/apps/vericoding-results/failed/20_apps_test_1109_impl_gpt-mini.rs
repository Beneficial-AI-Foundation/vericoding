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
/* helper modified by LLM (iteration 5): simple min for ints used in specs */
spec fn min_i(a: int, b: int) -> int {
    if a < b { a } else { b }
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
    /* code modified by LLM (iteration 5): iterate columns and rows, avoid creating Seq<int> in executable code; use spec-view a@ in invariants */
    let n_i: i32 = n as i32;
    let k_i: i32 = k as i32;
    let m_i: i32 = n_i / k_i;

    let mut col: i32 = 0;
    let mut acc: i32 = 0;

    while col < k_i
        invariant
            0 <= col as int <= k as int,
            col as int <= n as int,
            acc as int == sum_min_changes_helper(a@.map(|i, v| v as int), n as int, k as int, 0) - sum_min_changes_helper(a@.map(|i, v| v as int), n as int, k as int, col as int),
        decreases k as int - col as int
    {
        let mut t: i32 = 0;
        let mut ones: i32 = 0;
        let mut twos: i32 = 0;
        while t < m_i
            invariant
                0 <= t as int <= m_i as int,
                ones as int == Set::new(|jj: int| 0 <= jj < t as int && a@[(jj * k as int + col as int) as nat] == 1).len() as int,
                twos as int == Set::new(|jj: int| 0 <= jj < t as int && a@[(jj * k as int + col as int) as nat] == 2).len() as int,
            decreases m_i as int - t as int
        {
            let idx = (t * k_i + col) as usize;
            if a[idx] == 1_i8 {
                ones = ones + 1;
            } else {
                twos = twos + 1;
            }
            t = t + 1;
        }

        let minc: i32 = if ones < twos { ones } else { twos };
        acc = acc + minc;
        col = col + 1;
    }

    acc as i8
}

// </vc-code>


}

fn main() {}