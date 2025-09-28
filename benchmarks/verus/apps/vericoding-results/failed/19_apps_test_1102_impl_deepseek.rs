// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, a: int, x: Seq<int>) -> bool {
    n > 0 && 1 <= a <= n && x.len() == n && 
    forall|i: int| 0 <= i < n ==> (x[i] == 0 || x[i] == 1)
}

spec fn sum_criminals_caught(n: int, a_idx: int, x: Seq<int>, distance: int) -> int
    decreases n + 1 - distance
{
    if distance > n { 
        0
    } else {
        let le = a_idx - distance;
        let rg = a_idx + distance;
        let le_valid = le >= 0 && le < n;
        let rg_valid = rg >= 0 && rg < n;
        let current_caught = if !le_valid && !rg_valid {
            0
        } else if le_valid && !rg_valid {
            x[le]
        } else if !le_valid && rg_valid {
            x[rg]
        } else if le_valid && rg_valid && x[le] == 1 && x[rg] == 1 {
            2
        } else {
            0
        };
        if !le_valid && !rg_valid {
            current_caught
        } else {
            current_caught + sum_criminals_caught(n, a_idx, x, distance + 1)
        }
    }
}

spec fn total_criminals_caught(n: int, a: int, x: Seq<int>) -> int {
    x[a-1] + sum_criminals_caught(n, a-1, x, 1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type casting issues using proper ghost variables */
proof fn lemma_sum_criminals_caught_bound(n: int, a_idx: int, x: Seq<int>, distance: int)
    requires
        n > 0,
        0 <= a_idx < n,
        x.len() == n,
        forall|i: int| 0 <= i < n ==> (x[i] == 0 || x[i] == 1),
        distance >= 1,
    ensures
        sum_criminals_caught(n, a_idx, x, distance) >= 0,
    decreases n + 1 - distance
{
    if distance <= n {
        let le = a_idx - distance;
        let rg = a_idx + distance;
        let le_valid = le >= 0 && le < n;
        let rg_valid = rg >= 0 && rg < n;
        
        if le_valid {
            assert(0 <= le < n);
        }
        if rg_valid {
            assert(0 <= rg < n);
        }
        
        lemma_sum_criminals_caught_bound(n, a_idx, x, distance + 1);
    }
}

proof fn lemma_total_criminals_caught_bound(n: int, a_idx: int, x: Seq<int>)
    requires
        n > 0,
        0 <= a_idx < n,
        x.len() == n,
        forall|i: int| 0 <= i < n ==> (x[i] == 0 || x[i] == 1),
    ensures
        total_criminals_caught(n, a_idx + 1, x) >= 0,
{
    lemma_sum_criminals_caught_bound(n, a_idx, x, 1);
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: i8, x: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, a as int, Seq::new(x.len() as nat, |i: int| x[i] as int))
    ensures 
        result >= 0 &&
        result as int == total_criminals_caught(n as int, a as int, Seq::new(x.len() as nat, |i: int| x[i] as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation errors by using ghost variables for int math */
    let mut total: i8 = 0;
    let n_int = n;
    let a_idx: i8 = a - 1;
    let a_idx_int = a_idx;
    
    proof {
        let ghost n_val: int = n_int as int;
        let ghost a_idx_val: int = a_idx_int as int;
        let x_seq = Seq::new(x.len() as nat, |i| x[i] as int);
        lemma_total_criminals_caught_bound(n_val, a_idx_val, x_seq);
    }
    
    total += x[a_idx as usize];
    
    let mut distance: i8 = 1;
    while distance <= n
        invariant
            distance >= 1,
            total as int == x[a_idx_int as int] as int + sum_criminals_caught(n_int as int, a_idx_int as int, Seq::new(x.len() as nat, |i| x[i] as int), distance as int),
    {
        let le = a_idx - distance;
        let rg = a_idx + distance;
        
        if le >= 0 && le < n {
            total += x[le as usize];
        }
        if rg >= 0 && rg < n && rg != le {
            total += x[rg as usize];
        }
        
        distance += 1;
    }
    
    total
}
// </vc-code>


}

fn main() {}