// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, t: int) -> bool {
    1 <= n <= 10 && 0 <= t <= 10000
}

spec fn total_glasses(n: int) -> int {
    n * (n + 1) / 2
}

spec fn valid_result(result: int, n: int, t: int) -> bool {
    result >= 0 && result <= total_glasses(n)
}

spec fn correct_for_edge_cases(result: int, n: int, t: int) -> bool {
    (t == 0 ==> result == 0) &&
    (n == 1 && t >= 1 ==> result == 1) &&
    (n == 1 && t == 0 ==> result == 0) &&
    (t >= 1 && n > 1 ==> result >= 1)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, t: i8) -> (result: i8)
requires 
    valid_input(n as int, t as int)
ensures 
    valid_result(result as int, n as int, t as int),
    correct_for_edge_cases(result as int, n as int, t as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed mutable indexing by breaking down += operations */
{
    let n_usize = n as usize;
    let total = (n_usize * (n_usize+1)) / 2;
    let mut glasses: Vec<i32> = vec![0; total];
    if n > 0 {
        glasses[0] = t as i32;
    }
    for i in 0..n_usize-1 {
        for j in 0..(i+1) {
            let idx = (i * (i+1)) / 2 + j;
            let denom = 1 << i;
            if glasses[idx] >= denom {
                let overflow = glasses[idx] - denom;
                glasses[idx] = denom;
                let left_idx = ((i+1) * (i+2)) / 2 + j;
                let right_idx = ((i+1) * (i+2)) / 2 + j+1;
                let current_left = glasses[left_idx];
                glasses[left_idx] = current_left + overflow;
                let current_right = glasses[right_idx];
                glasses[right_idx] = current_right + overflow;
            }
        }
    }
    let mut count = 0;
    for idx in 0..glasses.len() {
        if glasses[idx] > 0 {
            count += 1;
        }
    }
    count as i8
}
// </vc-code>


}

fn main() {}