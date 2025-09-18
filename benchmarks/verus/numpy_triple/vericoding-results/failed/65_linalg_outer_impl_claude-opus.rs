// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn outer_i32(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<Vec<i32>>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == b.len(),
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result[i].len() ==> 
            result[i][j] == a[i] * b[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type conversion errors */
    let mut result: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k].len() == b.len(),
            forall|k: int, j: int| 0 <= k < i && 0 <= j < result[k].len() ==> result[k][j] == a[k] * b[j],
        decreases a.len() - i
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < b.len()
            invariant
                i < a.len(),
                j <= b.len(),
                row.len() == j,
                forall|k: int| 0 <= k < j ==> row@[k] == a@[i as int] * b@[k],
            decreases b.len() - j
        {
            let product: i32 = a[i] * b[j];
            row.push(product);
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