// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [use usize for exec code] */
fn interim_row_val(i: usize, j: usize) -> (val: f32) {
    if j == i + 1 {
        0.5f32
    } else if i > 0 && j == i - 1 {
        if i == 1 { 1.0f32 } else { 0.5f32 }
    } else {
        0.0f32
    }
}

/* helper modified by LLM (iteration 5): [use usize for exec code] */
fn last_row_val(c: &Vec<f32>, j: usize) -> (val: f32)
    requires
        c@.len() >= 2,
        j < c@.len() - 1,
{
    let n = c.len() - 1;
    let cn = c[n];
    if cn != 0.0f32 {
        let scl = if j < n - 1 {
            1.0f32 / (2.0f32 * cn)
        } else { // j == n - 1
            1.0f32 / cn
        };
        -c[j] * scl
    } else {
        0.0f32
    }
}
// </vc-helpers>

// <vc-spec>
fn chebcompanion(c: Vec<f32>) -> (result: Vec<Vec<f32>>)
    requires c@.len() >= 2,
    ensures
        result@.len() == c@.len() - 1,
        forall|i: int| 0 <= i < result@.len() ==> result@[i].len() == c@.len() - 1,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): [use usize for exec code] */
    let n = c.len() - 1;
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < n - 1
        invariant
            i <= n - 1,
            result@.len() == i,
            forall|k: int| 0 <= k < i ==> result@[k].len() == n,
        decreases n - 1 - i
    {
        let mut row: Vec<f32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                j <= n,
                row@.len() == j,
            decreases n - j
        {
            row.push(interim_row_val(i, j));
            j = j + 1;
        }
        result.push(row);
        i = i + 1;
    }

    let mut last_row: Vec<f32> = Vec::new();
    let mut j: usize = 0;
    while j < n
        invariant
            j <= n,
            last_row@.len() == j,
        decreases n - j
    {
        last_row.push(last_row_val(&c, j));
        j = j + 1;
    }
    result.push(last_row);
    
    result
}
// </vc-code>

}
fn main() {}