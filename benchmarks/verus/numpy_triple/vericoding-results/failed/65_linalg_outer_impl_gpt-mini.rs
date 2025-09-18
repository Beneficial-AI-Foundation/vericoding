// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): multiplication spec */
spec fn mul_i32(x: i32, y: i32) -> i32 { x * y }
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
    /* code modified by LLM (iteration 5): implemented outer product using nested while loops with separated invariants */
    let la: int = a.len();
    let lb: int = b.len();
    let mut result: Vec<Vec<i32>> = Vec::<Vec<i32>>::new();
    let mut i: int = 0;
    while i < la
        invariant 0 <= i;
        invariant i <= la;
        invariant result.len() == i;
        invariant forall|ii: int| 0 <= ii < i ==> result@[ii].len() == lb;
        invariant forall|ii: int| 0 <= ii < i ==> forall|j: int| 0 <= j < lb ==> result@[ii]@[j] == a@[ii] * b@[j];
        decreases la - i;
    {
        let mut row: Vec<i32> = Vec::<i32>::new();
        let mut j: int = 0;
        while j < lb
            invariant 0 <= j;
            invariant j <= lb;
            invariant row.len() == j;
            invariant forall|jj: int| 0 <= jj < j ==> row@[jj] == a@[i] * b@[jj];
            decreases lb - j;
        {
            row.push(a@[i] * b@[j]);
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