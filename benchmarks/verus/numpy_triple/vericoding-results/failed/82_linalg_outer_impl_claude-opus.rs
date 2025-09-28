// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): fixed int type usage in exec code */
    let mut result: Vec<Vec<i8>> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k].len() == b.len(),
            forall|k: int, j: int| 0 <= k < i && 0 <= j < result[k].len() ==>
                result[k][j] as int == a[k] as int * b[j] as int,
        decreases a.len() - i
    {
        let mut row: Vec<i8> = Vec::new();
        let mut j: usize = 0;
        while j < b.len()
            invariant
                i < a.len(),
                j <= b.len(),
                row.len() == j,
                forall|k: int| 0 <= k < j ==> row[k] as int == a[i] as int * b[k] as int,
            decreases b.len() - j
        {
            let ai = a[i];
            let bj = b[j];
            let product: i8 = (ai as i32 * bj as i32) as i8;
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