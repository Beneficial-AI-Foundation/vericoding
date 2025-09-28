// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma relating runtime and spec lengths for Vec */
proof fn v_len_consistent<T>(v: &Vec<T>)
    ensures
        v.len() as int == v@.len(),
{
    proof {
        assert(v.len() as int == v@.len());
    }
}

/* helper modified by LLM (iteration 5): lemma to expose equal inner row lengths uniformly */
proof fn condlist_row_lengths_equal_local(condlist: &Vec<Vec<bool>>, choicelist: &Vec<Vec<f32>>)
    requires
        condlist@.len() > 0,
        condlist@.len() == choicelist@.len(),
        forall|i: int| 0 <= i < condlist@.len() ==> condlist@[i].len() > 0,
        forall|i: int| 0 <= i < condlist@.len() ==> condlist@[i].len() == choicelist@[i].len(),
        forall|i: int, j: int| 0 <= i < condlist@.len() && 0 <= j < condlist@.len() ==> condlist@[i].len() == condlist@[j].len(),
    ensures
        forall|i: int| 0 <= i < condlist@.len() ==> condlist@[i].len() == condlist@[0].len(),
{
    proof {
        let m = condlist@.len();
        assert(m > 0);
        forall|i: int| {
            if (0 <= i && i < m) {
                // instantiate j = 0 from pairwise equality
                assert(0 <= 0 && 0 < m);
                assert(condlist@[i].len() == condlist@[0].len());
            }
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn select(condlist: Vec<Vec<bool>>, choicelist: Vec<Vec<f32>>) -> (result: Vec<f32>)
    requires 
        condlist@.len() > 0,
        condlist@.len() == choicelist@.len(),
        forall|i: int| 0 <= i < condlist@.len() ==> condlist@[i].len() > 0,
        forall|i: int| 0 <= i < condlist@.len() ==> condlist@[i].len() == choicelist@[i].len(),
        forall|i: int, j: int| 0 <= i < condlist@.len() && 0 <= j < condlist@.len() ==> 
            condlist@[i].len() == condlist@[j].len(),
    ensures
        result@.len() == condlist@[0].len(),
        forall|i: int, j: int| 
            0 <= i < condlist@.len() && 0 <= j < result@.len() && condlist@[i][j] ==> 
            result@[j] == choicelist@[i][j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement select with safe index proofs and renamed helpers */
    let n_rows: usize = condlist.len();
    let n_cols: usize = condlist[0].len();

    let mut result: Vec<f32> = Vec::new();

    let mut col: usize = 0;
    while col < n_cols
        invariant
            col <= n_cols,
        decreases (n_cols as int) - (col as int)
    {
        proof {
            v_len_consistent(&condlist[0]);
            v_len_consistent(&choicelist[0]);
            assert((condlist[0].len() as int) == condlist@[0].len());
            assert((choicelist[0].len() as int) == choicelist@[0].len());
            assert((col as int) < condlist@[0].len());
            assert((col as int) < choicelist@[0].len());
        }

        let mut chosen: f32 = choicelist[0][col];

        let mut row: usize = 0;
        while row < n_rows
            invariant
                row <= n_rows,
            decreases (n_rows as int) - (row as int)
        {
            proof {
                assert(row < condlist.len());
                v_len_consistent(&condlist[row]);
                v_len_consistent(&choicelist[row]);
                condlist_row_lengths_equal_local(&condlist, &choicelist);
                // relate col (usize) to spec lengths via 0-row equality
                assert((col as int) < condlist@[0].len());
                assert(condlist@[0].len() == condlist@[(row as int)].len());
                assert((col as int) < condlist@[(row as int)].len());
                assert(choicelist@[(row as int)].len() == condlist@[(row as int)].len());
                assert((col as int) < choicelist@[(row as int)].len());
            }

            if condlist[row][col] {
                chosen = choicelist[row][col];
                break;
            }
            row += 1;
        }

        result.push(chosen);
        col += 1;
    }

    result
}

// </vc-code>


}
fn main() {}