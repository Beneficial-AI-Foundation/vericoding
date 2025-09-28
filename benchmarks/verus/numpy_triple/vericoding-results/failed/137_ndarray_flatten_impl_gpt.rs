// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simple transitivity lemma for < */
proof fn lemma_lt_trans(a: int, b: int, c: int)
    requires
        a < b,
        b < c,
    ensures
        a < c,
{
    assert(a < c);
}
// </vc-helpers>

// <vc-spec>
fn flatten(mat: Vec<Vec<i8>>) -> (result: Vec<i8>)
    requires 
        mat@.len() > 0,
        forall|i: int| 0 <= i < mat@.len() ==> mat@[i].len() > 0,
        forall|i: int, j: int| 0 <= i < mat@.len() && 0 <= j < mat@.len() ==> mat@[i].len() == mat@[j].len(),
    ensures 
        result@.len() == mat@.len() * mat@[0].len(),
        forall|r: int, c: int| 
            0 <= r < mat@.len() && 0 <= c < mat@[0].len() ==>
            result@[r * mat@[0].len() + c] == mat@[r][c]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): add parentheses around casts in specs and clean up invariants */
    let rows: usize = mat.len();
    let cols: usize = mat[0].len();
    let rows_i: int = rows as int;
    let cols_i: int = cols as int;
    let mut result: Vec<i8> = Vec::new();
    let mut r: usize = 0;
    let mut c: usize = 0;

    while r < rows
        invariant
            mat@.len() == rows_i,
            rows_i > 0,
            cols_i > 0,
            r <= rows,
            c <= cols,
            forall|i: int, j: int| 0 <= i && i < rows_i && 0 <= j && j < rows_i ==> mat@[i].len() == mat@[j].len(),
            result@.len() == ((r as int) * cols_i + (c as int)),
            forall|rr: int, cc: int|
                0 <= rr && rr < (r as int) && 0 <= cc && cc < cols_i ==> result@[(rr * cols_i + cc)] == mat@[rr][cc],
            forall|cc: int| 0 <= cc && cc < (c as int) ==> result@[((r as int) * cols_i + cc)] == mat@[r as int][cc],
        decreases (rows - r) as int
    {
        while c < cols
            invariant
                mat@.len() == rows_i,
                rows_i > 0,
                cols_i > 0,
                r < rows,
                c <= cols,
                forall|i: int, j: int| 0 <= i && i < rows_i && 0 <= j && j < rows_i ==> mat@[i].len() == mat@[j].len(),
                result@.len() == ((r as int) * cols_i + (c as int)),
                forall|rr: int, cc: int|
                    0 <= rr && rr < (r as int) && 0 <= cc && cc < cols_i ==> result@[(rr * cols_i + cc)] == mat@[rr][cc],
                forall|cc: int| 0 <= cc && cc < (c as int) ==> result@[((r as int) * cols_i + cc)] == mat@[r as int][cc],
            decreases (cols - c) as int
        {
            let x = mat[r][c];
            let ghost c0: int = c as int;
            let old_len_usize = result.len();
            let old_len_int: int = old_len_usize as int;
            assert(old_len_int == (r as int) * cols_i + (c as int));
            let ghost old_result = result@;
            proof {
                assert_forall_by(|rr: int, cc: int| {
                    requires
                        0 <= rr && rr < (r as int) && 0 <= cc && cc < cols_i;
                    ensures
                        old_result[(rr * cols_i + cc)] == mat@[rr][cc];
                    assert(cols_i > 0);
                    assert(rr <= (r as int) - 1);
                    assert(rr * cols_i <= ((r as int) - 1) * cols_i);
                    assert(rr * cols_i + cc <= ((r as int) - 1) * cols_i + cc);
                    assert(cc < cols_i);
                    assert(((r as int) - 1) * cols_i + cc < ((r as int) - 1) * cols_i + cols_i);
                    assert(rr * cols_i + cc < (r as int) * cols_i);
                    assert((c as int) >= 0);
                    assert(rr * cols_i + cc < (r as int) * cols_i + (c as int));
                    assert(old_result == result@);
                    assert(old_result[(rr * cols_i + cc)] == result@[(rr * cols_i + cc)]);
                    assert(result@[(rr * cols_i + cc)] == mat@[rr][cc]);
                });
                assert_forall_by(|cc: int| {
                    requires
                        0 <= cc && cc < (c as int);
                    ensures
                        old_result[((r as int) * cols_i + cc)] == mat@[r as int][cc];
                    assert(((r as int) * cols_i + cc) < ((r as int) * cols_i + (c as int)));
                    assert(old_result == result@);
                    assert(old_result[((r as int) * cols_i + cc)] == result@[((r as int) * cols_i + cc)]);
                    assert(result@[((r as int) * cols_i + cc)] == mat@[r as int][cc]);
                });
            }
            result.push(x);
            proof {
                assert(result@.len() == old_result.len() + 1);
                assert(result@[old_result.len()] == x);
                assert_forall_by(|rr: int, cc: int| {
                    requires
                        0 <= rr && rr < (r as int) && 0 <= cc && cc < cols_i;
                    ensures
                        result@[(rr * cols_i + cc)] == mat@[rr][cc];
                    assert(old_result.len() == (r as int) * cols_i + (c as int));
                    assert(cols_i > 0);
                    assert(rr <= (r as int) - 1);
                    assert(rr * cols_i <= ((r as int) - 1) * cols_i);
                    assert(rr * cols_i + cc <= ((r as int) - 1) * cols_i + cc);
                    assert(cc < cols_i);
                    assert(((r as int) - 1) * cols_i + cc < ((r as int) - 1) * cols_i + cols_i);
                    assert(rr * cols_i + cc < (r as int) * cols_i);
                    assert((r as int) * cols_i <= (r as int) * cols_i + (c as int));
                    assert(rr * cols_i + cc < old_result.len());
                    assert(result@[(rr * cols_i + cc)] == old_result[(rr * cols_i + cc)]);
                    assert(old_result[(rr * cols_i + cc)] == mat@[rr][cc]);
                });
                assert_forall_by(|cc: int| {
                    requires
                        0 <= cc && cc < (c as int);
                    ensures
                        result@[((r as int) * cols_i + cc)] == mat@[r as int][cc];
                    assert((r as int) * cols_i + cc < old_result.len());
                    assert(result@[((r as int) * cols_i + cc)] == old_result[((r as int) * cols_i + cc)]);
                    assert(old_result[((r as int) * cols_i + cc)] == mat@[r as int][cc]);
                });
                assert(old_result.len() == (r as int) * cols_i + (c as int));
                assert(result@[((r as int) * cols_i + c0)] == x);
                assert(x == mat@[r as int][c0]);
            }
            c += 1;
            proof {
                assert(c as int == c0 + 1);
                assert_forall_by(|cc: int| {
                    requires
                        0 <= cc && cc < (c as int);
                    ensures
                        result@[((r as int) * cols_i + cc)] == mat@[r as int][cc];
                    if cc < (c as int) - 1 {
                        assert(result@[((r as int) * cols_i + cc)] == mat@[r as int][cc]);
                    } else {
                        assert(cc == (c as int) - 1);
                        assert(cc == c0);
                        assert(result@[((r as int) * cols_i + cc)] == result@[((r as int) * cols_i + c0)]);
                        assert(result@[((r as int) * cols_i + cc)] == x);
                        assert(x == mat@[r as int][cc]);
                    }
                });
            }
        }
        r += 1;
        c = 0;
        proof {
            let r_done: int = (r as int) - 1;
            assert(0 <= r_done && r_done < rows_i);
            assert(result@.len() == ((r as int) * cols_i + (c as int)));
            assert(result@.len() == (r as int) * cols_i);
            assert_forall_by(|rr: int, cc: int| {
                requires
                    0 <= rr && rr < (r as int) && 0 <= cc && cc < cols_i;
                ensures
                    result@[(rr * cols_i + cc)] == mat@[rr][cc];
                if rr < r_done {
                    assert(result@[(rr * cols_i + cc)] == mat@[rr][cc]);
                } else {
                    assert(rr == r_done);
                    assert(result@[(r_done * cols_i + cc)] == mat@[r_done][cc]);
                }
            });
        }
    }
    proof {
        assert(cols_i == mat[0].len() as int);
        assert(mat[0].len() as int == mat@[0].len());
        assert(cols_i == mat@[0].len());
    }
    result
}
// </vc-code>

}
fn main() {}