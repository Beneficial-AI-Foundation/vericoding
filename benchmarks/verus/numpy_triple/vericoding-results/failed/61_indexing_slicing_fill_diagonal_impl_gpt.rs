// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): simple arithmetic lemma about min on nat values */
pub proof fn lemma_min_nat_components(a: nat, b: nat, i: nat)
    requires
        i < if a < b { a } else { b },
    ensures
        i < a,
        i < b,
{
    if a < b {
        assert(i < a);
        assert(a <= b);
    } else {
        assert(i < b);
        assert(b <= a);
    }
}
// </vc-helpers>

// <vc-spec>
fn fill_diagonal<T: Copy>(mat: Vec<Vec<T>>, val: T) -> (result: Vec<Vec<T>>)
    requires 
        mat@.len() > 0,
        forall|i: int| 0 <= i < mat@.len() ==> #[trigger] mat@[i].len() == mat@[0].len(),
    ensures
        result@.len() == mat@.len(),
        forall|i: int| 0 <= i < result@.len() ==> #[trigger] result@[i].len() == mat@[i].len(),

        forall|i: int, j: int| 
            0 <= i < result@.len() && 0 <= j < result@[i].len() && i == j 
            ==> #[trigger] result@[i][j] == val,

        forall|i: int, j: int| 
            0 <= i < result@.len() && 0 <= j < result@[i].len() && i != j 
            ==> #[trigger] result@[i][j] == mat@[i][j]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fix forall proofs to use implies; add bound assertions before Vec indexing; construct each row and push */
    let rows = mat.len();
    assert(rows as int == mat@.len());
    assert(0 < mat@.len());

    let cols = mat[0].len();
    assert(cols as int == mat@[0].len());

    assert forall|i: int| 0 <= i && i < mat@.len() implies #[trigger] mat@[i].len() == cols as int by {
        if 0 <= i && i < mat@.len() {
            assert(mat@[i].len() == mat@[0].len());
            assert(cols as int == mat@[0].len());
        }
    };

    let mut result: Vec<Vec<T>> = Vec::new();
    let mut r: usize = 0;
    while r < rows
        invariant
            rows as int == mat@.len(),
            cols as int == mat@[0].len(),
            result@.len() == r as int,
            forall|i: int| 0 <= i && i < result@.len() implies #[trigger] result@[i].len() == cols as int,
            forall|i: int, j: int|
                0 <= i && i < result@.len() && 0 <= j && j < result@[i].len() && i == j
                implies #[trigger] result@[i][j] == val,
            forall|i: int, j: int|
                0 <= i && i < result@.len() && 0 <= j && j < result@[i].len() && i != j
                implies #[trigger] result@[i][j] == mat@[i][j],
            0 <= r as int,
            r as int <= rows as int,
        decreases rows - r
    {
        assert((r as int) < mat@.len());

        let mut row_vec: Vec<T> = Vec::new();
        let mut c: usize = 0;
        while c < cols
            invariant
                rows as int == mat@.len(),
                cols as int == mat@[0].len(),
                (r as int) < mat@.len(),
                row_vec@.len() == c as int,
                0 <= c as int,
                c as int <= cols as int,
                forall|j: int|
                    0 <= j && j < row_vec@.len()
                    implies #[trigger] row_vec@[j] == (if r as int == j { val } else { mat@[r as int][j] }),
            decreases cols - c
        {
            assert((c as int) < cols as int);
            assert((r as int) < mat@.len());
            assert(mat@[r as int].len() == mat@[0].len());
            assert(cols as int == mat@[0].len());
            assert((c as int) < mat@[r as int].len());

            let elem = if r == c { val } else { mat[r][c] };
            row_vec.push(elem);
            c += 1;
        }
        assert(row_vec@.len() == cols as int);

        assert forall|j: int|
            0 <= j && j < row_vec@.len() && r as int == j implies #[trigger] row_vec@[j] == val by {
            if 0 <= j && j < row_vec@.len() && r as int == j {
                assert(row_vec@[j] == (if r as int == j { val } else { mat@[r as int][j] }));
            }
        };
        assert forall|j: int|
            0 <= j && j < row_vec@.len() && r as int != j implies #[trigger] row_vec@[j] == mat@[r as int][j] by {
            if 0 <= j && j < row_vec@.len() && r as int != j {
                assert(row_vec@[j] == (if r as int == j { val } else { mat@[r as int][j] }));
            }
        };

        result.push(row_vec);
        r += 1;
    }

    assert(result@.len() == mat@.len());
    assert forall|i: int|
        0 <= i && i < result@.len() implies #[trigger] result@[i].len() == mat@[i].len() by {
        if 0 <= i && i < result@.len() {
            assert(result@[i].len() == cols as int);
            assert(result@.len() == mat@.len());
            assert(0 < mat@.len());
            assert(cols as int == mat@[0].len());
            assert(mat@[i].len() == mat@[0].len());
        }
    };

    result
}
// </vc-code>

}
fn main() {}