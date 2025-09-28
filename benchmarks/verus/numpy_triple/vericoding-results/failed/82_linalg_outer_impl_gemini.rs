// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added trigger to fix quantifier inference and used spec indexing */
fn compute_row(a_i: i8, b: &Vec<i8>) -> (row: Vec<i8>)
    requires
        forall|j: int| 0 <= j < b.len() ==> i8::MIN <= (a_i as int * #[trigger] b@[j] as int) <= i8::MAX,
    ensures
        row.len() == b.len(),
        forall|j: int| 0 <= j < b.len() ==> row@[j] as int == a_i as int * b@[j] as int,
{
    let mut row: Vec<i8> = Vec::new();
    let mut j: usize = 0;
    while j < b.len()
        invariant
            j <= b.len(),
            row.len() == j,
            forall|l: int| 0 <= l < j ==> row@[l] as int == a_i as int * b@[l] as int,
        decreases b.len() - j
    {
        let val = a_i * b[j];
        row.push(val);
        j = j + 1;
    }
    row
}
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
/* code modified by LLM (iteration 5): using spec indexing in invariants */
{
    let mut result: Vec<Vec<i8>> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result@[k].len() == b.len(),
            forall|k: int, l: int|
                0 <= k < i && 0 <= l < b.len() ==>
                result@[k]@[l] as int == a@[k] as int * b@[l] as int,
        decreases a.len() - i
    {
        let row = compute_row(a[i], &b);
        result.push(row);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}