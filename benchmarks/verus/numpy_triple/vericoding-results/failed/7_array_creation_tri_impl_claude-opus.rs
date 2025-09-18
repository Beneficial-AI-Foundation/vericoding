// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn tri(n: usize, m: usize, k: i32) -> (result: Vec<Vec<f64>>)
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n ==> result[i].len() == m,
        forall|i: int, j: int| 0 <= i < n && 0 <= j < m ==> 
            result[i][j] == if j <= i + k { 1.0 } else { 0.0 }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed integer overflow and invariant preservation */
    let mut result: Vec<Vec<f64>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|x: int| 0 <= x < i ==> result[x].len() == m,
            forall|x: int, y: int| 0 <= x < i && 0 <= y < m ==> 
                result[x][y] == if y <= x + k { 1.0 } else { 0.0 }
        decreases n - i
    {
        let mut row: Vec<f64> = Vec::new();
        let mut j: usize = 0;
        while j < m
            invariant
                j <= m,
                row.len() == j,
                forall|y: int| 0 <= y < j ==> 
                    row[y] == if y <= i as int + k { 1.0 } else { 0.0 }
            decreases m - j
        {
            if j as int <= i as int + k {
                row.push(1.0);
            } else {
                row.push(0.0);
            }
            proof {
                assert(row.len() == j + 1);
                assert(forall|y: int| 0 <= y < j + 1 ==> 
                    row[y] == if y <= i as int + k { 1.0 } else { 0.0 });
            }
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