// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn eye(n: usize) -> (result: Vec<Vec<f32>>)
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n ==> #[trigger] result[i].len() == n,
        forall|i: int, j: int| 0 <= i < n && 0 <= j < n ==> 
            result[i][j] == if i == j { 1.0f32 } else { 0.0f32 },
        forall|i: int, j: int| 0 <= i < n && 0 <= j < n ==> 
            result[i][j] == result[j][i],
        forall|i: int, j:int| 0 <= i <= j < n ==> (#[trigger] result[i][j] == 1.0f32 ==> i == j),
        forall|i: int, j: int| 0 <= i < n && 0 <= j < n && i != j ==> 
            result[i][j] == 0.0f32,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Fixed postcondition verification by using assert statements */
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            result.len() == i,
            i <= n,
            forall|k: int| 0 <= k < i ==> #[trigger] result[k as int].len() == n,
            forall|k: int, j: int| 0 <= k < i && 0 <= j < n ==> 
                result[k as int][j as int] == if k == j { 1.0f32 } else { 0.0f32 },
        decreases n - i
    {
        let mut row: Vec<f32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                row.len() == j,
                j <= n,
                forall|k: int| 0 <= k < j ==> 
                    row[k as int] == if i as int == k { 1.0f32 } else { 0.0f32 },
            decreases n - j
        {
            if i == j {
                row.push(1.0f32);
            } else {
                row.push(0.0f32);
            }
            j = j + 1;
        }
        assert(row.len() == n);
        assert(forall|k: int| 0 <= k < n ==> row[k as int] == if i as int == k { 1.0f32 } else { 0.0f32 });
        result.push(row);
        i = i + 1;
    }
    assert(result.len() == n);
    assert(forall|k: int| 0 <= k < n ==> result[k as int].len() == n);
    assert(forall|k: int, j: int| 0 <= k < n && 0 <= j < n ==> 
        result[k as int][j as int] == if k == j { 1.0f32 } else { 0.0f32 });
    result
}
// </vc-code>

}
fn main() {}