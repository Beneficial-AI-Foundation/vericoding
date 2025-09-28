// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn polycompanion(c: Vec<i8>) -> (result: Vec<Vec<i8>>)
    requires 
        c.len() >= 2,
        c[c.len() - 1] != 0,
    ensures
        result.len() == c.len() - 1,
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == c.len() - 1,
        forall|i: int, j: int| 
            0 <= i < result.len() && 0 <= j < result[i].len() ==>
            (if i + 1 == j && i < c.len() - 2 {
                result[i][j] as int == 1
            } else if i == c.len() - 2 {
                result[i][j] as int * c[c.len() - 1] as int == -c[j] as int
            } else {
                result[i][j] as int == 0
            })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): added missing function body braces */
    let n = c.len();
    let n_minus_1 = n - 1;
    let n_int = n as int;
    let n_minus_1_int = n_minus_1 as int;
    
    let mut result: Vec<Vec<i8>> = Vec::new();
    let mut i = 0;
    while i < n_minus_1
        invariant 
            0 <= i <= n_minus_1_int,
            result.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] result[k].len() == n_minus_1_int,
        decreases n_minus_1_int - i
    {
        let mut row: Vec<i8> = Vec::new();
        let mut j = 0;
        while j < n_minus_1
            invariant 
                0 <= j <= n_minus_1_int,
                row.len() == j,
            decreases n_minus_1_int - j
        {
            let i_int = i as int;
            let j_int = j as int;
            
            assert(0 <= j_int < n_int);
            
            let value: i8;
            if i_int + 1 == j_int && i_int < n_minus_1_int - 1 {
                value = 1;
            } else if i_int == n_minus_1_int - 1 {
                let numerator = -c[j];
                let denominator = c[n-1];
                let numerator_int = numerator as int;
                let denominator_int = denominator as int;
                value = (numerator_int / denominator_int) as i8;
            } else {
                value = 0;
            }
            
            row.push(value);
            j += 1;
        }
        result.push(row);
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}