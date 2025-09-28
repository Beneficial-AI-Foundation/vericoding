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
    let a_idx = (a - 1) as usize;
    let mut result: i8 = x[a_idx];
    let mut distance: usize = 1;
    
    while distance <= n as usize
        invariant
            0 < distance <= n as usize + 1,
            a_idx == (a - 1) as usize,
            result >= 0,
            result as int == x[a_idx] as int + sum_criminals_caught(n as int, a_idx as int, Seq::new(x.len() as nat, |i: int| x[i] as int), 1) - sum_criminals_caught(n as int, a_idx as int, Seq::new(x.len() as nat, |i: int| x[i] as int), distance as int),
        decreases n as usize + 1 - distance
    {
        let le = if a_idx >= distance { a_idx - distance } else { n as usize };
        let rg = a_idx + distance;
        
        let le_valid = le < n as usize;
        let rg_valid = rg < n as usize;
        
        if !le_valid && !rg_valid {
            distance = distance + 1;
            continue;
        }
        
        if le_valid && !rg_valid {
            result = result + x[le];
        } else if !le_valid && rg_valid {
            result = result + x[rg];
        } else if le_valid && rg_valid {
            if x[le] == 1 && x[rg] == 1 {
                result = result + 2;
            }
        }
        
        distance = distance + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}