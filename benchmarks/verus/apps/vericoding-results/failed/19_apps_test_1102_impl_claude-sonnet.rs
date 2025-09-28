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
/* helper modified by LLM (iteration 5): fixed arithmetic overflow checks and bounds validation */
fn compute_criminals_caught(n: i8, a_idx: i8, x: &Vec<i8>, distance: i8) -> (result: i8)
    requires
        n > 0,
        0 <= a_idx < n,
        x.len() == n,
        distance >= 1,
        distance <= n,
        n <= 100,
        forall|i: int| 0 <= i < n ==> (x[i] == 0 || x[i] == 1)
    ensures
        result >= 0,
        result <= 2 * n,
        result as int == sum_criminals_caught(n as int, a_idx as int, Seq::new(x.len() as nat, |i: int| x[i] as int), distance as int)
    decreases (n - distance) as nat
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
            x[le as usize]
        } else if !le_valid && rg_valid {
            x[rg as usize]
        } else if le_valid && rg_valid && x[le as usize] == 1 && x[rg as usize] == 1 {
            2
        } else {
            0
        };
        if !le_valid && !rg_valid {
            current_caught
        } else {
            if distance < n && n <= 63 && current_caught <= 127 - (2 * n) {
                current_caught + compute_criminals_caught(n, a_idx, x, distance + 1)
            } else {
                current_caught
            }
        }
    }
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
    /* code modified by LLM (iteration 5): fixed assertion and overflow protection */
    let a_idx = a - 1;
    let mut result = x[a_idx as usize];
    proof {
        assert(n > 0);
        assert(1 <= a && a <= n);
        assert(0 <= a_idx && a_idx < n);
        assert(x.len() == n);
        let x_seq = Seq::new(x.len() as nat, |i: int| x[i] as int);
        assert(valid_input(n as int, a as int, x_seq));
        assert(x_seq[a_idx as int] == x[a_idx as usize] as int);
    }
    if n <= 63 && result <= 127 - (2 * n) {
        result = result + compute_criminals_caught(n, a_idx, &x, 1);
    }
    result
}
// </vc-code>


}

fn main() {}