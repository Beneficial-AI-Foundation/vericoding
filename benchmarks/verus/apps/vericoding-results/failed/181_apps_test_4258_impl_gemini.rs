// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int, t: int) -> bool {
    1 <= a <= 20 && 1 <= b <= 20 && 1 <= t <= 20
}

spec fn production_count(a: int, t: int) -> int {
    if a > 0 { t / a } else { 0 }
}

spec fn total_biscuits(a: int, b: int, t: int) -> int {
    if a > 0 { b * production_count(a, t) } else { 0 }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, t: i8) -> (result: i8)
    requires valid_input(a as int, b as int, t as int)
    ensures result as int == total_biscuits(a as int, b as int, t as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation error */
    let a_int = a as int;
    let b_int = b as int;
    let t_int = t as int;

    let num_productions = t as i32 / a as i32;
    let total = num_productions * (b as i32);

    proof {
        let num_productions_spec = production_count(a_int, t_int);
        let total_spec = total_biscuits(a_int, b_int, t_int);

        // Prove executable division matches spec division
        vstd::arithmetic::div_mod::lemma_div_is_spec_for_pos(t_int, a_int);
        assert(num_productions as int == num_productions_spec);

        // Prove executable multiplication matches spec multiplication
        // First establish bounds to show i32 doesn't overflow.
        vstd::arithmetic::div_mod::lemma_div_is_le(t_int, a_int);
        assert(num_productions_spec <= t_int);
        assert(num_productions_spec <= 20);
        assert(0 <= num_productions_spec);
        assert(0 <= b_int <= 20);

        vstd::arithmetic::nonlin::lemma_mul_le(num_productions_spec, b_int, 20, 20);
        assert(total_spec <= 400);

        assert(i32::MIN as int <= total_spec <= i32::MAX as int);
        vstd::arithmetic::mul::lemma_mul_is_spec(num_productions, b as i32);

        assert(total as int == total_spec);
    }

    // The ensurse clause is unsatisfiable for inputs where `total_spec` > 127.
    // Since the task is to fix the implementation, not the spec, this is the most
    // correct implementation possible; it computes the required value and relies on
    // the verifier to report the contradiction with the return type.
    total as i8
}
// </vc-code>


}

fn main() {}