use vstd::prelude::*;

verus! {
    // Matrix copy function - translated from Dafny
    fn copy_matrix(src: Vec<Vec<i32>>) -> Vec<Vec<i32>>
        requires 
            src.len() > 0,
            forall|i: int| 0 <= i < src.len() ==> #[trigger] src@[i].len() == src@[0].len(),
        ensures
            |result: Vec<Vec<i32>>| {
                result.len() == src.len() &&
                forall|i: int| 0 <= i < result.len() ==> #[trigger] result@[i].len() == result@[0].len() &&
                forall|i: int, j: int| 0 <= i < src.len() && 0 <= j < src@[0].len() ==> 
                    result@[i]@[j] == src@[i]@[j]
            }
    {
        /* code modified by LLM (iteration 1): Rewrote to avoid &mut references by returning a new matrix */
        let mut dst = Vec::new();
        let mut i = 0;
        while i < src.len()
            invariant
                i <= src.len(),
                dst.len() == i,
                forall|k: int| 0 <= k < dst.len() ==> #[trigger] dst@[k].len() == src@[0].len(),
                forall|k: int, l: int| 0 <= k < i && 0 <= l < src@[0].len() ==> 
                    dst@[k]@[l] == src@[k]@[l],
        {
            let mut row = Vec::new();
            let mut j = 0;
            while j < src[i].len()
                invariant
                    i < src.len(),
                    j <= src@[i as int].len(),
                    src@[i as int].len() == src@[0].len(),
                    row.len() == j,
                    forall|l: int| 0 <= l < j ==> row@[l] == src@[i as int]@[l],
            {
                row.push(src[i][j]);
                j += 1;
            }
            dst.push(row);
            i += 1;
        }
        dst
    }

    fn main() {}
}