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
    /* code modified by LLM (iteration 2): use int for indices, fix accesses, use while loops with invariants */
    let n: int = c.view().len() - 1;
    let mut result: Vec<Vec<i8>> = Vec::new();
    let mut i: int = 0;
    while i < n
        invariant
            0 <= i <= n,
            result.view().len() == i,
            forall |k: int| 0 <= k < i ==> result.view()[k].view().len() == n,
        decreases n - i
    {
        let mut row: Vec<i8> = Vec::new();
        let mut j: int = 0;
        while j < n
 Zjednoc            invariant
                0 <= j <= n,
                row.view().len() == j,
            decreases n - j
        {
            if (i + 1) == j && i < n - 1 {
                row.push(1);
            } else if i == n - 1 {
                let last: i8 = c.view()[n];
                let val: int = ( - (c.view()[j] as int) ) / (last as int);
                row.push(val as i8);
            } else {
                row.push(0);
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