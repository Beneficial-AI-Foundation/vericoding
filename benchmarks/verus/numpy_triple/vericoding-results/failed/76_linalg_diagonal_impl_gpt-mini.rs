// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prove bounds for n = min(rows, cols) using int types */
fn lemma_n_bounds(rows: int, cols: int, n: int)
    requires
        n == if rows <= cols { rows } else { cols },
    ensures
        n <= rows,
        n <= cols,
{
    if rows <= cols {
        assert(n == rows);
        assert(n <= rows);
        assert(rows <= cols);
        assert(n <= cols);
    } else {
        assert(n == cols);
        assert(n <= cols);
        assert(cols < rows);
        assert(n <= rows);
    }
}

// </vc-helpers>

// <vc-spec>
spec fn spec_min(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

fn numpy_diagonal(x: Vec<Vec<f32>>, offset: i32) -> (result: Vec<f32>)
    requires 
        x@.len() > 0,
        x@.len() < usize::MAX,
        forall|i: int| 0 <= i < x@.len() ==> #[trigger] x@[i].len() > 0,
        forall|i: int| 0 <= i < x@.len() ==> #[trigger] x@[i].len() == x@[0].len(),
    ensures
        result@.len() == spec_min(x@.len() as int, x@[0].len() as int),
        offset == 0 ==> forall|i: int| 0 <= i < result@.len() ==> 
            result@[i] == x@[i][i],
        forall|i: int| 0 <= i < result@.len() ==> 
            exists|r: int, c: int| 
                0 <= r < x@.len() && 0 <= c < x@[0].len() &&
                #[trigger] result@[i] == x@[r][c],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): implement diagonal extraction using int indices and proofs */
{
    let rows: int = x.len() as int;
    let cols: int = x[0].len() as int;
    let n: int = if rows <= cols { rows } else { cols };

    let mut result: Vec<f32> = Vec::new();
    let mut i: int = 0;

    while i < n
        invariant
            0 <= i,
            i <= n,
            result.len() as int == i,
        decreases n - i
    {
        proof {
            assert(i < n);
            lemma_n_bounds(rows, cols, n);
            assert(n <= rows);
            assert(n <= cols);
            assert(i < rows);
            assert(i < cols);
        }
        result.push(x[i][i]);
        i = i + 1;
    }

    proof {
        assert(result.len() as int == n);
        assert(result@.len() == n);
        assert(result@.len() == spec_min(rows, cols));

        if offset == 0 {
            let mut k: int = 0;
            while k < result.len() as int
                invariant
                    0 <= k,
                    k <= result.len() as int,
                decreases result.len() as int - k
            {
                proof {
                    assert(result[k] == x[k][k]);
                    assert(result@[k] == result[k]);
                    assert(x@[k]@[k] == x[k][k]);
                    assert(result@[k] == x@[k]@[k]);
                }
                k = k + 1;
            }
        }

        let mut k2: int = 0;
        while k2 < result.len() as int
            invariant
                0 <= k2,
                k2 <= result.len() as int,
            decreases result.len() as int - k2
        {
            proof {
                lemma_n_bounds(rows, cols, n);
                assert(k2 < rows);
                assert(k2 < cols);
                assert(result@[k2] == x@[k2]@[k2]);
            }
            k2 = k2 + 1;
        }
    }

    result
}

// </vc-code>

}
fn main() {}