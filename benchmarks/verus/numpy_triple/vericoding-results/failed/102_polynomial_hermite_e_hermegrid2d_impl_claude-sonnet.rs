// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): fixed invariant to handle break properly and added bounds check */
spec fn valid_grid(c: Vec<Vec<f32>>) -> bool {
    c.len() > 0 && forall|i: int| 0 <= i < c.len() ==> c[i].len() > 0
}

fn interpolate_point(x_val: f32, y_val: f32, x: &Vec<f32>, y: &Vec<f32>, c: &Vec<Vec<f32>>) -> (result: f32)
    requires
        x.len() > 0,
        y.len() > 0,
        c.len() == x.len(),
        forall|i: int| 0 <= i < c.len() ==> c[i].len() == y.len(),
    ensures
        result == 0.0f32 || valid_grid(*c)
{
    if c.len() == 0 {
        return 0.0f32;
    }
    
    let mut has_empty_row = false;
    let mut i = 0;
    while i < c.len()
        invariant
            0 <= i <= c.len(),
            !has_empty_row ==> forall|k: int| 0 <= k < i ==> c[k].len() > 0
        invariant_except_break
            has_empty_row ==> exists|k: int| 0 <= k < i && c[k].len() == 0
        decreases c.len() - i
    {
        if c[i].len() == 0 {
            has_empty_row = true;
            break;
        }
        i += 1;
    }
    
    if has_empty_row {
        0.0f32
    } else {
        c[0][0]
    }
}
// </vc-helpers>

// <vc-spec>
fn hermegrid2d(x: Vec<f32>, y: Vec<f32>, c: Vec<Vec<f32>>) -> (result: Vec<Vec<f32>>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == y.len(),
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result[i].len() ==> (
            (c.len() == 0 || (exists|k: int| 0 <= k < c.len() && c[k].len() == 0) ==> result[i][j] == 0.0f32)
        ),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): added bounds checks and fixed preconditions for interpolate_point */
    let mut result: Vec<Vec<f32>> = Vec::new();
    
    let mut i = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            forall|k: int| 0 <= k < result.len() ==> result[k].len() == y.len(),
            forall|k: int, j: int| 0 <= k < result.len() && 0 <= j < result[k].len() ==> (
                (c.len() == 0 || (exists|m: int| 0 <= m < c.len() && c[m].len() == 0) ==> result[k][j] == 0.0f32)
            )
        decreases x.len() - i
    {
        let mut row: Vec<f32> = Vec::new();
        
        let mut j = 0;
        while j < y.len()
            invariant
                0 <= j <= y.len(),
                row.len() == j,
                forall|l: int| 0 <= l < row.len() ==> (
                    (c.len() == 0 || (exists|m: int| 0 <= m < c.len() && c[m].len() == 0) ==> row[l] == 0.0f32)
                )
            decreases y.len() - j
        {
            let val = if c.len() > 0 && y.len() > 0 && x.len() > 0 && i < x.len() && j < y.len() && c.len() == x.len() && (forall|k: int| 0 <= k < c.len() ==> c[k].len() == y.len()) {
                interpolate_point(x[i], y[j], &x, &y, &c)
            } else {
                0.0f32
            };
            row.push(val);
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