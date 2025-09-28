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
    /* code modified by LLM (iteration 2): Fixed compilation error by removing int casts in exec code */
    let n = c.len() - 1;
    let mut result: Vec<Vec<i8>> = Vec::new();
    let mut i = 0;
    
    while i < n
        invariant
            n == c.len() - 1,
            c.len() >= 2,
            c[c.len() - 1] != 0,
            0 <= i <= n,
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k].len() == n,
            forall|k: int, j: int| 
                0 <= k < i && 0 <= j < n ==>
                (if k + 1 == j && k < n - 1 {
                    result[k][j] as int == 1
                } else if k == n - 1 {
                    result[k][j] as int * c[n] as int == -c[j] as int
                } else {
                    result[k][j] as int == 0
                }),
    {
        let mut row: Vec<i8> = Vec::new();
        let mut j = 0;
        
        while j < n
            invariant
                n == c.len() - 1,
                c.len() >= 2,
                c[c.len() - 1] != 0,
                0 <= i < n,
                0 <= j <= n,
                row.len() == j,
                forall|k: int|
                    0 <= k < j ==>
                    (if i + 1 == k && i < n - 1 {
                        row[k] as int == 1
                    } else if i == n - 1 {
                        row[k] as int * c[n] as int == -c[k] as int
                    } else {
                        row[k] as int == 0
                    }),
        {
            if i + 1 == j && i < n - 1 {
                row.push(1);
            } else if i == n - 1 {
                let val = -c[j] / c[n];
                row.push(val);
            } else {
                row.push(0);
            }
            j = j + 1;
        }
        
        result.push(row);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}