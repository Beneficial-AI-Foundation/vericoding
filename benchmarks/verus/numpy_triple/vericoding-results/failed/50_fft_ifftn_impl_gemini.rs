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
{
    /* code modified by LLM (iteration 5): add explicit triggers and remove redundant assert */
    let rows = a.len();
    let cols = a[0].len();

    let mut result: Vec<Vec<i8>> = Vec::new();
    let mut i: usize = 0;

    while i < rows
        invariant
            0 <= i <= rows,
            a.len() == rows,
            forall|k: int| 0 <= k < a@.len() ==> a@[k].len() == cols as int,
            result.len() == i,
            result@.len() == i as int,
            forall|k: int| 0 <= k < i as int ==> #[trigger] result@[k].len() == cols as int,
            forall|k: int, l: int|
                (0 <= k < i as int && 0 <= l < result@[k].len()) ==> #[trigger] result@[k]@[l] == 0i8,
        decreases rows - i
    {
        let mut new_row: Vec<i8> = Vec::new();
        let mut j: usize = 0;
        while j < cols
            invariant
                0 <= j <= cols,
                new_row.len() == j,
                new_row@.len() == j as int,
                forall|k: int| 0 <= k < j as int ==> #[trigger] new_row@[k] == 0i8,
            decreases cols - j
        {
            new_row.push(0i8);
            j = j + 1;
        }
        result.push(new_row);
        i = i + 1;
    }

    result
}
// </vc-code>


}
fn main() {}