// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn abs_val(x: int) -> int {
    if x >= 0 { x } else { -x }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): basic max function for ints */
spec fn max_int(a: int, b: int) -> int { if a >= b { a } else { b } }

/* helper modified by LLM (iteration 5): abs non-negativity lemma */
proof fn lemma_abs_nonneg(x: int)
    ensures
        abs_val(x) >= 0,
{
    if x >= 0 {
        assert(abs_val(x) == x);
    } else {
        assert(abs_val(x) == -x);
        assert(-x >= 0);
    }
}

/* helper modified by LLM (iteration 5): abs zero implies value zero */
proof fn lemma_abs_zero_implies_zero(x: int)
    ensures
        abs_val(x) == 0 ==> x == 0,
{
    if x >= 0 {
        assert(abs_val(x) == x);
    } else {
        assert(abs_val(x) == -x);
        assert(-x == 0 ==> x == 0);
    }
}

/* helper modified by LLM (iteration 5): value zero implies abs zero */
proof fn lemma_zero_implies_abs_zero(x: int)
    ensures
        x == 0 ==> abs_val(x) == 0,
{
    if x >= 0 {
        assert(abs_val(x) == x);
    } else {
        assert(abs_val(x) == -x);
    }
}

/* helper modified by LLM (iteration 5): non-zero implies abs positive */
proof fn lemma_nonzero_implies_abs_pos(x: int)
    ensures
        x != 0 ==> abs_val(x) > 0,
{
    if x > 0 {
        assert(abs_val(x) == x);
        assert(x > 0);
    } else if x < 0 {
        assert(abs_val(x) == -x);
        assert(-x > 0);
    } else {
        // vacuous
    }
}

// </vc-helpers>

// <vc-spec>
fn matrix_norm(x: Vec<Vec<i8>>) -> (result: i8)
    requires 
        x@.len() > 0,
        forall|i: int| 0 <= i < x@.len() ==> #[trigger] x@[i].len() > 0,
        forall|i: int| 0 <= i < x@.len() ==> #[trigger] x@[i].len() == x@[0].len(),
    ensures
        result as int >= 0,
        (result as int == 0) == (forall|i: int, j: int| 
            0 <= i < x@.len() && 0 <= j < x@[i].len() ==> #[trigger] x@[i][j] == 0),
        forall|i: int, j: int| 
            0 <= i < x@.len() && 0 <= j < x@[i].len() ==> abs_val(#[trigger] x@[i][j] as int) <= result as int,
        (exists|i: int, j: int| 
            0 <= i < x@.len() && 0 <= j < x@[i].len() && #[trigger] x@[i][j] != 0) ==> result as int > 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed invariant references to use `rows` instead of `x@.len()` to resolve parse error; preserved logic and proofs */
    let rows: usize = x.len();

    let mut i: usize = 0;
    let mut max_abs: int = 0;
    let ghost mut have_witness: bool = false;
    let ghost mut wi: int = 0;
    let ghost mut wj: int = 0;

    while i < rows
        invariant
            0 <= i as int && i as int <= rows as int,
            rows as int == x@.len(),
            max_abs >= 0,
            forall|ii: int, jj: int|
                0 <= ii && ii < i as int && 0 <= jj && jj < x@[ii].len() ==> abs_val(#[trigger] x@[ii][jj] as int) <= max_abs,
            (have_witness ==> 0 <= wi && wi < i as int && 0 <= wj && wj < x@[wi].len() && max_abs == abs_val(x@[wi][wj] as int)),
            (!have_witness ==> max_abs == 0),
        decreases rows as int - i as int
    {
        let cols: usize = x[i].len();
        let mut j: usize = 0;
        while j < cols
            invariant
                0 <= i as int && i as int < rows as int,
                0 <= j as int && j as int <= cols as int,
                cols as int == x@[i as int].len(),
                max_abs >= 0,
                forall|ii: int, jj: int|
                    0 <= ii && ii < i as int && 0 <= jj && jj < x@[ii].len() ==> abs_val(#[trigger] x@[ii][jj] as int) <= max_abs,
                forall|jj: int|
                    0 <= jj && jj < j as int ==> abs_val(#[trigger] x@[i as int][jj] as int) <= max_abs,
                (have_witness ==> ((0 <= wi && wi < i as int) || (wi == i as int && 0 <= wj && wj < j as int)) && max_abs == abs_val(x@[wi][wj] as int)),
                (!have_witness ==> max_abs == 0),
            decreases cols as int - j as int
        {
            let v_i8: i8 = x[i][j];
            let v_int: int = v_i8 as int;
            let abs_ij: int = abs_val(v_int);
            proof {
                if v_int >= 0 {
                    assert(abs_ij == v_int);
                } else {
                    assert(abs_ij == -v_int);
                }
                assert(abs_ij >= 0);
            }
            if abs_ij > max_abs {
                max_abs = abs_ij;
                proof {
                    have_witness = true;
                    wi = i as int;
                    wj = j as int;
                }
            }
            j = j + 1;
        }
        proof {
            assert(j == cols);
            assert(j as int == cols as int);
            assert(cols as int == x@[i as int].len());
            assert(forall|jj: int| 0 <= jj && jj < x@[i as int].len() ==> abs_val(#[trigger] x@[i as int][jj] as int) <= max_abs);
        }
        i = i + 1;
    }

    let result_i8: i8 = if max_abs <= 127 { max_abs as i8 } else { 127i8 };

    result_i8
}
// </vc-code>


}
fn main() {}