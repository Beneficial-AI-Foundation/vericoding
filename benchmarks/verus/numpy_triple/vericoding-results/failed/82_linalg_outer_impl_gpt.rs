// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): retain simple spec multiplication helper for reasoning about values as ints */
pub open spec fn mul_as_int(x: i8, y: i8) -> int { (x as int) * (y as int) }
// </vc-helpers>

// <vc-spec>
fn outer_i32(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<Vec<i8>>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == b.len(),
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result[i].len() ==> 
            result[i][j] as int == a[i] as int * b[j] as int,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix usize/int index mismatch in invariants by casting indices to int where needed */
    let n = a.len();
    let m = b.len();
    let mut result: Vec<Vec<i8>> = Vec::new();

    let mut i: usize = 0;
    while i < n
        invariant
            result.len() == i,
            i <= n,
            n == a.len(),
            m == b.len(),
            forall|ii: int| 0 <= ii < result.len() as int ==> result[ii].len() == m,
            forall|ii: int, jj: int|
                0 <= ii < result.len() as int && 0 <= jj < result[ii].len() as int ==>
                    result[ii][jj] as int == a[ii] as int * b[jj] as int,
        decreases (n - i) as int
    {
        let mut row: Vec<i8> = Vec::new();
        let mut j: usize = 0;
        while j < m
            invariant
                i < n,
                row.len() == j,
                j <= m,
                n == a.len(),
                m == b.len(),
                forall|jj: int|
                    0 <= jj < row.len() as int ==> row[jj] as int == a[i as int] as int * b[jj] as int,
            decreases (m - j) as int
        {
            let ai = a[i];
            let bj = b[j];
            let prod: i8 = ai * bj;
            row.push(prod);
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