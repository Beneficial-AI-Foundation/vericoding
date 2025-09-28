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
fn sum_criminals_caught_iterative(n: int, a_idx: int, x: Seq<int>) -> (result: int)
    requires valid_input(n, a_idx + 1, x)
    ensures result == sum_criminals_caught(n, a_idx, x, 1)
{
    let mut total = 0;
    let mut distance = 1;
    
    while distance <= n
        invariant
            1 <= distance <= n + 1,
            total == sum_criminals_caught(n, a_idx, x, distance),
        decreases n + 1 - distance
    {
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
        
        total = total + current_caught;
        distance = distance + 1;
    }
    
    total
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
    let x_seq = Seq::new(x.len() as nat, |i: int| x[i] as int);
    let a_idx = (a - 1) as int;
    let caught_at_a = x_seq[a_idx];
    let caught_elsewhere = sum_criminals_caught_iterative(n as int, a_idx, x_seq);
    (caught_at_a + caught_elsewhere) as i8
}
// </vc-code>


}

fn main() {}