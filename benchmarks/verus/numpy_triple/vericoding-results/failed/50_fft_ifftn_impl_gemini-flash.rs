// <vc-preamble>
use vstd::prelude::*;

verus! {

/* Sum of integers over finite indices */
pub open spec fn int_sum(n: nat, f: spec_fn(int) -> int) -> int
    decreases n
{
    if n == 0 {
        0
    } else {
        f((n - 1) as int) + int_sum((n - 1) as nat, f)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): removed unused `use std::ops::IndexMut;` to fix compilation error and removed `lemma_int_sum_associativity` as it was unused and unrelated to the task */
// </vc-helpers>

// <vc-spec>
fn ifftn(a: Vec<Vec<i8>>) -> (result: Vec<Vec<i8>>)
    requires 
        a.len() > 0,
        a.len() < usize::MAX,
        forall|i: int| 0 <= i < a@.len() ==> a@[i].len() > 0,
        forall|i: int| 0 <= i < a@.len() ==> a@[i].len() < usize::MAX,
        forall|i: int, j: int| 0 <= i < a@.len() && 0 <= j < a@.len() ==> a@[i].len() == a@[j].len(),
    ensures 
        result@.len() == a@.len(),
        forall|i: int| 0 <= i < result@.len() ==> result@[i].len() == a@[0].len(),
        forall|i: int, j: int| #[trigger] result@[i][j] == 0 || 
            (0 <= i < result@.len() && 0 <= j < result@[i].len()),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fixed type mismatch in forall quantifier using `as int` conversion */
{
    let rows = a.len();
    let cols = a[0].len();

    let mut result: Vec<Vec<i8>> = Vec::new();
    while result.len() < rows
        invariant
            result.len() <= rows,
            forall|i: int| 0 <= i < result.len() ==> result@[i].len() == cols,
    {
        let mut row_vec: Vec<i8> = Vec::new();
        while row_vec.len() < cols
            invariant
                row_vec.len() <= cols,
        {
            row_vec.push(0);
        }
        result.push(row_vec);
    }

    let mut r = 0;
    while r < rows
        invariant
            r <= rows,
            result.len() == rows,
            forall|i: int| 0 <= i < result.len() ==> result@[i].len() == cols,
            forall|i: int, j: int| 0 <= i < r && 0 <= j < cols ==> result@[i][j] == 0,
    {
        let mut c = 0;
        while c < cols
            invariant
                c <= cols,
                r < rows,
                result.len() == rows,
                forall|i: int| 0 <= i < result.len() ==> result@[i].len() == cols,
                forall|k: int| 0 <= k < c ==> result@[r][k as usize] == 0,
                forall|i: int, j: int| 0 <= i < r && 0 <= j < cols ==> result@[i][j] == 0,
        {
            *result.index_mut(r).index_mut(c) = 0;
            c = c + 1;
        }
        r = r + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}