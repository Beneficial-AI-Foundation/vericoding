use vstd::prelude::*;

verus! {
    // Matrix copy function - translated from Dafny
    fn copy_matrix(src: Vec<Vec<i32>>, dst: &mut Vec<Vec<i32>>)
        requires 
            src.len() == old(dst).len(),
            src.len() > 0,
            old(dst).len() > 0,
            forall|i: int| 0 <= i < src.len() ==> #[trigger] src@[i].len() == src@[0].len(),
            forall|i: int| 0 <= i < old(dst).len() ==> #[trigger] old(dst)@[i].len() == old(dst)@[0].len(),
            src@[0].len() == old(dst)@[0].len(),
        ensures
            dst.len() == src.len(),
            forall|i: int| 0 <= i < dst.len() ==> #[trigger] dst@[i].len() == dst@[0].len(),
            forall|i: int, j: int| 0 <= i < src.len() && 0 <= j < src@[0].len() ==> 
                dst@[i]@[j] == src@[i]@[j],
    {
        let mut i = 0;
        while i < src.len()
            invariant
                i <= src.len(),
                dst.len() == src.len(),
                forall|k: int| 0 <= k < dst.len() ==> #[trigger] dst@[k].len() == dst@[0].len(),
                forall|k: int, l: int| 0 <= k < i && 0 <= l < src@[0].len() ==> 
                    dst@[k]@[l] == src@[k]@[l],
        {
            let mut j = 0;
            while j < src[i].len()
                invariant
                    i < src.len(),
                    j <= src@[i as int].len(),
                    src@[i as int].len() == src@[0].len(),
                    dst@[i as int].len() == dst@[0].len(),
                    dst.len() == src.len(),
                    forall|k: int| 0 <= k < dst.len() ==> #[trigger] dst@[k].len() == dst@[0].len(),
                    forall|k: int, l: int| 0 <= k < i && 0 <= l < src@[0].len() ==> 
                        dst@[k]@[l] == src@[k]@[l],
                    forall|l: int| 0 <= l < j ==> dst@[i as int]@[l] == src@[i as int]@[l],
            {
                /* code modified by LLM (iteration 1): Fixed mutable reference indexing issue by using get_mut instead of direct indexing */
                let dst_row = dst.get_mut(i).unwrap();
                dst_row.set(j, src[i][j]);
                j += 1;
            }
            i += 1;
        }
    }

    fn main() {}
}