// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type conversion errors in executable code */
spec fn abs(x: i8) -> i8 {
    if x < 0 { (-x) as i8 } else { x }
}

spec fn max_spec(a: i8, b: i8) -> i8 {
    if a >= b { a } else { b }
}

fn compute_max(a: i8, b: i8) -> (result: i8)
    ensures
        result == max_spec(a, b)
{
    if a >= b { a } else { b }
}

fn matrix_norm_inf(x: &Vec<Vec<i8>>) -> (result: i8)
    requires
        x.len() > 0,
        forall|i: int| 0 <= i < x.len() ==> x[i].len() == x.len()
    ensures
        result >= 0
{
    let n = x.len();
    let mut max_sum: i8 = 0;
    let mut i: usize = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            max_sum >= 0,
            n == x.len(),
            forall|k: int| 0 <= k < x.len() ==> x[k].len() == x.len(),
        decreases n - i
    {
        let mut row_sum: i8 = 0;
        let mut j: usize = 0;
        
        while j < n
            invariant
                0 <= j <= n,
                row_sum >= 0,
                row_sum <= 127,
                i < n,
                n == x.len(),
                forall|k: int| 0 <= k < x.len() ==> x[k].len() == x.len(),
            decreases n - j
        {
            let val = x[i][j];
            let abs_val: i8 = if val == -128i8 { 
                127i8
            } else if val < 0 {
                (-val) as i8
            } else {
                val
            };
            
            if row_sum <= 127 - abs_val {
                row_sum = row_sum + abs_val;
            } else {
                row_sum = 127;
            }
            j = j + 1;
        }
        
        max_sum = compute_max(max_sum, row_sum);
        i = i + 1;
    }
    
    max_sum
}
// </vc-helpers>

// <vc-spec>
fn condition_number(x: Vec<Vec<i8>>) -> (result: i8)
    requires 
        x.len() > 0,
        forall|i: int| 0 <= i < x.len() ==> x[i].len() == x.len(),
    ensures 
        result as int >= 0,
        result as int >= 1,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): No changes needed in main code */
    let norm = matrix_norm_inf(&x);
    if norm == 0 {
        1
    } else {
        norm
    }
}
// </vc-code>


}
fn main() {}