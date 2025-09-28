// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, m: int) -> bool {
    n >= 1 && m >= 1
}

spec fn count_face_down_cards(n: int, m: int) -> int
    recommends valid_input(n, m)
{
    if n == 1 && m == 1 {
        1
    } else if n == 1 {
        m - 2
    } else if m == 1 {
        n - 2
    } else {
        (n - 2) * (m - 2)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): prove non-negativity of count_face_down_cards */
proof fn lemma_count_nonneg(n: int, m: int)
    requires
        valid_input(n, m),
    ensures
        count_face_down_cards(n, m) >= 0,
{
    if n == 1 && m == 1 {
        assert(count_face_down_cards(n, m) == 1);
    } else if n == 1 {
        assert(m >= 1);
        assert(!(m == 1));
        assert(m > 1);
        assert(m >= 2);
        assert(count_face_down_cards(n, m) == m - 2);
        assert(m - 2 >= 0);
    } else if m == 1 {
        assert(n >= 1);
        assert(!(n == 1));
        assert(n > 1);
        assert(n >= 2);
        assert(count_face_down_cards(n, m) == n - 2);
        assert(n - 2 >= 0);
    } else {
        assert(n >= 1 && m >= 1);
        assert(!(n == 1));
        assert(!(m == 1));
        assert(n > 1 && m > 1);
        assert(n >= 2 && m >= 2);
        assert(count_face_down_cards(n, m) == (n - 2) * (m - 2));
        assert(n - 2 >= 0 && m - 2 >= 0);
        assert((n - 2) * (m - 2) >= 0);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8) -> (result: i8)
    requires 
        valid_input(n as int, m as int),
    ensures 
        result as int == count_face_down_cards(n as int, m as int),
        result >= 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): compute using i8 only and add proofs for nonnegativity and simple-case equalities */
    let result_local: i8;
    if n == 1 && m == 1 {
        result_local = 1;
        proof { assert(result_local as int == 1); }
    } else if n == 1 {
        result_local = m - 2;
        proof { assert(result_local as int == m as int - 2); }
    } else if m == 1 {
        result_local = n - 2;
        proof { assert(result_local as int == n as int - 2); }
    } else {
        result_local = (n - 2) * (m - 2);
    }
    proof {
        lemma_count_nonneg(n as int, m as int);
        if n == 1 && m == 1 {
            assert(result_local as int == count_face_down_cards(n as int, m as int));
        } else if n == 1 {
            assert(result_local as int == count_face_down_cards(n as int, m as int));
        } else if m == 1 {
            assert(result_local as int == count_face_down_cards(n as int, m as int));
        } else {
            // Equality for the general case will be addressed in a subsequent iteration.
        }
    }
    result_local
}
// </vc-code>


}

fn main() {}