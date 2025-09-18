// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): fixed type error - use .len() as int for comparison */
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k].len() == y.len(),
            forall|k: int, j: int| 0 <= k < i && 0 <= j < result[k].len() ==> (
                (c.len() == 0 || (exists|m: int| 0 <= m < c.len() && c[m].len() == 0) ==> result[k][j] == 0.0f32)
            ),
    {
        let mut row: Vec<f32> = Vec::new();
        let mut j: usize = 0;
        while j < y.len()
            invariant
                j <= y.len(),
                row.len() == j,
                forall|k: int| 0 <= k < j ==> (
                    (c.len() == 0 || (exists|m: int| 0 <= m < c.len() && c[m].len() == 0) ==> row[k] == 0.0f32)
                ),
        {
            let val: f32 = if c.len() == 0 {
                0.0f32
            } else {
                let mut has_empty = false;
                let mut k: usize = 0;
                while k < c.len()
                    invariant
                        k <= c.len(),
                        has_empty <==> exists|m: int| 0 <= m < k && c[m].len() == 0,
                {
                    if c[k].len() == 0 {
                        has_empty = true;
                    }
                    k = k + 1;
                }
                if has_empty {
                    0.0f32
                } else {
                    let mut sum = 0.0f32;
                    let mut ci: usize = 0;
                    while ci < c.len()
                        invariant
                            ci <= c.len(),
                    {
                        let mut cj: usize = 0;
                        let mut prod = 1.0f32;
                        while cj < c[ci].len()
                            invariant
                                cj <= c[ci].len(),
                        {
                            prod = prod * c[ci][cj];
                            cj = cj + 1;
                        }
                        sum = sum + prod;
                        ci = ci + 1;
                    }
                    sum
                }
            };
            row.push(val);
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