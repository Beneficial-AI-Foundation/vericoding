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
    /* code modified by LLM (iteration 5): replaced int with usize in loop conditions and indexing */
    let mut result: Vec<Vec<i8>> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k as usize].len() == b.len(),
            forall|k: int, l: int| 0 <= k < i && 0 <= l < result[k as usize].len() ==> 
                result[k as usize][l as usize] as int == a[k as usize] as int * b[l as usize] as int,
        decreases a.len() - i
    {
        let mut row: Vec<i8> = Vec::new();
        let mut j: usize = 0;
        while j < b.len()
            invariant
                0 <= j <= b.len(),
                row.len() == j,
                forall|l: int| 0 <= l < j ==> row[l as usize] as int == a[i as usize] as int * b[l as usize] as int,
            decreases b.len() - j
        {
            row.push(((a[i] as i32) * (b[j] as i32)) as i8);
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