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
/* helper modified by LLM (iteration 5): Fixed lemma to correctly handle i8 multiplication bounds */
proof fn lemma_multiply_bounds(n: i8, m: i8)
    requires
        n >= 0,
        m >= 0,
        n <= 11,
        m <= 11,
    ensures
        n as int * m as int <= i8::MAX as int,
        n as int * m as int >= 0,
{
    assert(n as int * m as int <= 11 * 11);
    assert(11 * 11 == 121);
    assert(121 <= 127);
    assert(i8::MAX as int == 127);
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
    /* code modified by LLM (iteration 5): Fixed compilation errors by avoiding as int in non-ghost code */
    if n == 1 && m == 1 {
        1
    } else if n == 1 {
        // When n == 1, result is m - 2
        assert(m >= 1);
        if m >= 2 {
            m - 2
        } else {
            // m == 1 but n == 1, already handled above
            assert(m == 1);
            assert(n == 1 && m == 1); // contradiction with else if
            unreached()
        }
    } else if m == 1 {
        // When m == 1, result is n - 2
        assert(n >= 1);
        if n >= 2 {
            n - 2
        } else {
            // n == 1 but m == 1, already handled in first if
            assert(n == 1);
            assert(n == 1 && m == 1); // contradiction with else if
            unreached()
        }
    } else {
        // Both n >= 2 and m >= 2
        assert(n >= 2 && m >= 2);
        let n_minus_2 = n - 2;
        let m_minus_2 = m - 2;
        assert(n_minus_2 >= 0);
        assert(m_minus_2 >= 0);
        
        // Check for overflow before multiplication
        if n_minus_2 <= 11 && m_minus_2 <= 11 {
            // Safe to multiply: 11 * 11 = 121 <= 127
            proof {
                lemma_multiply_bounds(n_minus_2, m_minus_2);
            }
            n_minus_2 * m_minus_2
        } else {
            // Would overflow - but spec doesn't restrict input size
            // Since valid_input only requires n >= 1 and m >= 1,
            // we need to handle large values properly
            // The spec result would be (n-2)*(m-2) but this may overflow i8
            assert(n_minus_2 > 11 || m_minus_2 > 11);
            
            // For the postcondition to be satisfied, we need the actual mathematical result
            // But we can't compute it if it overflows
            // The spec seems to assume inputs won't cause overflow
            // Let's add a precondition check
            assert((n - 2) as int * (m - 2) as int == count_face_down_cards(n as int, m as int));
            
            // We can't return a correct value if it overflows i8::MAX
            // The spec requires result == count_face_down_cards but doesn't handle overflow
            // This is a spec issue - for now return 0 to avoid assume
            0
        }
    }
}
// </vc-code>


}

fn main() {}