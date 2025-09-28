// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Helper lemma to prove invariant preservation */
lemma lemma_invariant_preserved(
    result: Vec<Vec<i8>>, 
    new_row: Vec<i8>, 
    i: usize, 
    n: usize, 
    c: Vec<i8>
)
    requires
        n >= 2,
        i < n - 1,
        new_row.len() == n - 1,
        forall|idx: int| 0 <= idx < new_row.len() ==>
            (if i + 1 == idx && i < n - 2 {
                new_row[idx] as int == 1
            } else if i == n - 2 {
                new_row[idx] as int * c[n - 1] as int == -c[idx] as int
            } else {
                new_row[idx] as int == 0
            }),
        forall|k: int, j: int| 
            0 <= k < result.len() && 0 <= j < result[k].len() ==>
            (if k + 1 == j && k < n - 2 {
                result[k][j] as int == 1
            } else if k == n - 2 {
                result[k][j] as int * c[n - 1] as int == -c[j] as int
            } else {
                result[k][j] as int == 0
            })
    ensures
        forall|k: int, j: int| 
            0 <= k < result.len() + 1 && 0 <= j < (if k < result.len() { result[k].len() } else { new_row.len() }) ==>
            (if k + 1 == j && k < n - 2 {
                (if k < result.len() { result[k][j] } else { new_row[j] }) as int == 1
            } else if k == n - 2 {
                (if k < result.len() { result[k][j] } else { new_row[j] }) as int * c[n - 1] as int == -c[j] as int
            } else {
                (if k < result.len() { result[k][j] } else { new_row[j] }) as int == 0
            })
{
}
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
    /* code modified by LLM (iteration 5): Fixed invariant and bounds checking with proper overflow protection */
    let n = c.len();
    let mut result: Vec<Vec<i8>> = Vec::new();
    
    let mut i = 0;
    while i < n - 1
        invariant
            0 <= i <= n - 1,
            n >= 2,
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k].len() == n - 1,
            forall|k: int, j: int| 
                0 <= k < i && 0 <= j < result[k].len() ==>
                (if k + 1 == j && k < n - 2 {
                    result[k][j] as int == 1
                } else if k == n - 2 {
                    result[k][j] as int * c[n - 1] as int == -c[j] as int
                } else {
                    result[k][j] as int == 0
                })
        decreases n - 1 - i
    {
        let mut row: Vec<i8> = Vec::new();
        let mut j = 0;
        
        while j < n - 1
            invariant
                0 <= j <= n - 1,
                0 <= i < n - 1,
                n >= 2,
                row.len() == j,
                forall|idx: int| 0 <= idx < j ==>
                    (if i + 1 == idx && i < n - 2 {
                        row[idx] as int == 1
                    } else if i == n - 2 && idx < c.len() - 1 {
                        row[idx] as int * c[n - 1] as int == -c[idx] as int
                    } else {
                        row[idx] as int == 0
                    })
            decreases n - 1 - j
        {
            let val = if i + 1 == j && i < n - 2 {
                1i8
            } else if i == n - 2 && j < c.len() - 1 && c[n - 1] != 0 {
                let numerator = -(c[j] as i16);
                let denominator = c[n - 1] as i16;
                (numerator / denominator) as i8
            } else {
                0i8
            };
            row.push(val);
            j += 1;
        }
        
        proof {
            lemma_invariant_preserved(result, row, i, n, c);
        }
        
        result.push(row);
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}