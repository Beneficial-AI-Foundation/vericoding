// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn spec_min_int(a: usize, b: usize) -> usize {
    if a < b { a } else { b }
}

fn min_int(a: usize, b: usize) -> (result: usize)
    ensures result == spec_min_int(a, b)
{
    if a < b { a } else { b }
}

/* helper modified by LLM (iteration 4): removed min_int_equiv_exec_spec and added ensures to min_int */
/* helper modified by LLM (iteration 3): new proof connecting spec_min_int to spec_min */
proof fn min_int_spec_to_spec_min(a: usize, b: usize)
    ensures spec_min_int(a, b) as int == spec_min(a as int, b as int)
{
    if a < b {
        assert(spec_min_int(a, b) == a);
        assert(a as int <= b as int);
        assert(spec_min(a as int, b as int) == a as int);
    } else {
        assert(spec_min_int(a, b) == b);
        assert(a as int >= b as int);
        assert(spec_min(a as int, b as int) == b as int);
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
{
    /* code modified by LLM (iteration 5): changed to while loop with invariants and added proof block for postconditions */
    let n_rows = x.len();
    let n_cols = x[0].len();
    let len = min_int(n_rows, n_cols);

    proof {
        min_int_spec_to_spec_min(n_rows, n_cols);
        // Now we know: len as int == spec_min(n_rows as int, n_cols as int)
    }

    let mut result = Vec::with_capacity(len);
    let mut i = 0;
    while i < len
        invariant 
            0 <= i <= len,
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == x@[j][j],
        decreases len - i
    {
        // We need to establish the indexing bounds for x[i][i]
        proof {
            // Since i < len and len <= n_rows and len <= n_cols, and all rows have length n_cols:
            assert(i < n_rows);
            assert(i < n_cols);
            // And because all rows have the same length (n_cols), we have:
            assert(x@[i].len() == n_cols);
            // Therefore:
            assert(i < x@.len());
            assert(i < x@[i].len());
        }
        result.push(x[i][i]);
        i += 1;
    }

    proof {
        // Now we have:
        //   result@.len() == len (from the loop invariant at the end: i==len)
        //   and we have len as int == spec_min(n_rows as int, n_cols as int)
        //   and n_rows = x@.len(), n_cols = x@[0].len()
        // Therefore: result@.len() == spec_min(x@.len() as int, x@[0].len() as int)
        assert(result@.len() == spec_min(x@.len() as int, x@[0].len() as int));
    }

    result
}
// </vc-code>

}
fn main() {}