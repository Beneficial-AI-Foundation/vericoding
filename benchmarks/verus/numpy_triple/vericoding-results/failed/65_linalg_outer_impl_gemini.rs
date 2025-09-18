// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): removed redundant overflow invariant inside the loop */
fn inner_product_row(val: i32, b: &Vec<i32>) -> (row: Vec<i32>)
    requires
        forall|j: int| 0 <= j < b.len() ==> i32::MIN <= (val as int) * (b@[j] as int) <= i32::MAX,
    ensures
        row.len() == b.len(),
        forall|j: int| 0 <= j < b.len() ==> row@[j] == val * b@[j],
{
    let mut row = Vec::new();
    let mut j: usize = 0;
    while j < b.len()
        invariant
            j <= b.len(),
            row.len() == j,
            forall|k: int| 0 <= k < j ==> row@[k] == val * b@[k],
            forall|idx: int| 0 <= idx < b.len() ==> i32::MIN <= (val as int) * (b@[idx] as int) <= i32::MAX,
        decreases b.len() - j
    {
        let item = val * b[j];
        row.push(item);
        j = j + 1;
    }
    row
}
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
    /* code modified by LLM (iteration 4): declared current_i as ghost to fix compilation error */
    let mut result: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result@[k].len() == b.len(),
            forall|k: int, l: int|
                0 <= k < i && 0 <= l < b.len() ==> result@[k]@[l] == a@[k] * b@[l],
        decreases a.len() - i
    {
        let ghost current_i = i as int;
        assert forall|j: int| 0 <= j < b.len() implies i32::MIN <= (a@[current_i] as int) * (b@[j] as int) <= i32::MAX by {};

        let row = inner_product_row(a[i], &b);
        result.push(row);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}