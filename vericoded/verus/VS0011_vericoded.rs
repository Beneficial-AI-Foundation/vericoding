// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): removed manual triggers */
fn get_column(input: &Vec<Vec<i8>>, j: usize, m: usize, n: usize) -> (col: Vec<i8>)
    requires
        n > 0,
        input@.len() == n,
        forall|i: int| 0 <= i < n ==> input@[i].len() == m,
        j < m,
    ensures
        col@.len() == n,
        forall|i: int| 0 <= i < n ==> col@[i] as int == input@[i]@[j as int] as int,
{
    let mut new_row: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n > 0,
            0 <= i <= n,
            j < m,
            input@.len() == n,
            forall|idx: int| 0 <= idx < n ==> input@[idx].len() == m,
            new_row@.len() == i,
            forall|l: int| 0 <= l < i ==> new_row@[l] as int == input@[l]@[j as int] as int,
        decreases n - i
    {
        let val = input[i][j];
        new_row.push(val);
        i = i + 1;
    }
    new_row
}
// </vc-helpers>

// <vc-spec>
fn column_stack(input: Vec<Vec<i8>>, m: usize, n: usize) -> (result: Vec<Vec<i8>>)
    requires 
        n > 0,
        input@.len() == n,
        forall|i: int| 0 <= i < n ==> #[trigger] input@[i].len() == m,
    ensures
        result@.len() == m,
        forall|j: int| 0 <= j < m ==> result@[j].len() == n,
        result@.len() * n == m * n,
        forall|i: int, j: int| 0 <= i < n && 0 <= j < m ==> 
            result@[j][i] as int == input@[i][j] as int,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): removed manual triggers */
    let mut result: Vec<Vec<i8>> = Vec::new();
    let mut j: usize = 0;
    while j < m
        invariant
            n > 0,
            0 <= j <= m,
            input@.len() == n,
            forall|i: int| 0 <= i < n ==> input@[i].len() == m,
            result@.len() == j,
            forall|k: int| 0 <= k < j ==> result@[k].len() == n,
            forall|k: int, l: int| 0 <= k < j && 0 <= l < n ==> 
                result@[k]@[l] as int == input@[l]@[k] as int,
        decreases m - j
    {
        let new_row = get_column(&input, j, m, n);
        result.push(new_row);
        j = j + 1;
    }
    result
}
// </vc-code>


}
fn main() {}