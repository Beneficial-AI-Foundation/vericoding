// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): relate usize min to spec_min for lengths */
proof fn lemma_min_usize_equals_spec_min(rows: usize, cols: usize)
    ensures
        (if rows <= cols { rows } else { cols }) as int == spec_min(rows as int, cols as int),
{
    if rows <= cols {
        assert(rows as int <= cols as int);
        assert(spec_min(rows as int, cols as int) == rows as int);
    } else {
        assert(!(rows as int <= cols as int));
        assert(spec_min(rows as int, cols as int) == cols as int);
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
    /* code modified by LLM (iteration 5): fix Seq indexing after push and maintain invariants */
    assert(x.len() > 0);
    let rows: usize = x.len();
    let cols: usize = x[0].len();

    let m: usize = if rows <= cols { rows } else { cols };

    proof { lemma_min_usize_equals_spec_min(rows, cols); }
    assert(rows as int == x@.len());
    assert(cols as int == x@[0].len());
    assert(m as int == spec_min(x@.len() as int, x@[0].len() as int));

    if rows <= cols {
        assert(m == rows);
        assert(m <= rows);
        assert(m <= cols);
    } else {
        assert(m == cols);
        assert(m <= rows);
        assert(m <= cols);
    }

    let mut result: Vec<f32> = Vec::new();
    let mut i: usize = 0;

    while i < m
        invariant
            x@.len() > 0,
            forall|j:int| 0 <= j < x@.len() ==> #[trigger] x@[j].len() > 0,
            forall|j:int| 0 <= j < x@.len() ==> #[trigger] x@[j].len() == x@[0].len(),
            m as int == spec_min(x@.len() as int, x@[0].len() as int),
            m <= rows,
            m <= cols,
            result@.len() == i as int,
            i <= m,
            forall|k:int| 0 <= k < result@.len() ==> #[trigger] result@[k] == x@[k][k],
        decreases m as int - i as int
    {
        assert(i < m);
        assert(i < rows);
        assert(i < cols);

        let v = x[i][i];
        result.push(v);

        assert(result@.len() == i as int + 1);

        assert forall|k:int|
            0 <= k && k < result@.len() implies #[trigger] result@[k] == x@[k][k]
        by {
            if 0 <= k && k < result@.len() {
                assert(result@ == old(&mut result)@.push(v));
                assert(old(&mut result)@.len() == i as int);
                if k < i as int {
                    assert(k < old(&mut result)@.len());
                    assert(result@[k] == old(&mut result)@.push(v)[k]);
                    assert(old(&mut result)@.push(v)[k] == old(&mut result)@[k]);
                    assert(old(&mut result)@[k] == x@[k][k]);
                } else {
                    assert(k >= i as int);
                    assert(k < i as int + 1);
                    assert(k == i as int);
                    assert(result@[k] == v);
                    assert(v == x@[i as int][i as int]);
                    assert(x@[i as int][i as int] == x@[k][k]);
                }
            }
        };

        i = i + 1;
    }

    assert(i == m);
    assert(result@.len() == m as int);
    assert(result@.len() == spec_min(x@.len() as int, x@[0].len() as int));

    assert forall|t:int|
        0 <= t && t < result@.len() implies
            exists|r:int, c:int|
                0 <= r < x@.len() && 0 <= c < x@[0].len() && #[trigger] result@[t] == x@[r][c]
    by {
        if 0 <= t && t < result@.len() {
            assert(result@[t] == x@[t][t]);
            assert(result@.len() == m as int);
            assert(m as int <= rows as int);
            assert(m as int <= cols as int);
            assert(rows as int == x@.len());
            assert(cols as int == x@[0].len());
            assert(0 <= t && t < x@.len());
            assert(0 <= t && t < x@[0].len());
            assert(exists|r:int, c:int| r == t && c == t && result@[t] == x@[r][c]);
        }
    };

    result
}
// </vc-code>

}
fn main() {}