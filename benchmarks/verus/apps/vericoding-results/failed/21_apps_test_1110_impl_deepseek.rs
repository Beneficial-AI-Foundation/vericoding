// <vc-preamble>
use vstd::prelude::*;

verus! {
    spec fn valid_input(n: int) -> bool {
        n >= 1
    }
    
    spec fn worst_case_presses(n: int) -> int
        recommends valid_input(n)
    {
        n * (n * n + 5) / 6
    }
// </vc-preamble>

// <vc-helpers>

    proof fn sum_of_squares_lemma(n: nat) -> (s: nat)
        ensures s == n * (n + 1) * (2 * n + 1) / 6,
        decreases n
    {
        if n > 0 {
            let prev = sum_of_squares_lemma((n - 1) as nat);
            s = prev + n * n;
        } else {
            s = 0;
        }
    }
    
    proof fn worst_case_formula_lemma(n: nat)
        ensures worst_case_presses(n) == n * (n * n + 5) / 6,
        decreases n
    {
        sum_of_squares_lemma(n);
    }

// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures result as int == worst_case_presses(n as int) && result as int >= 1
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed computation with proper type handling */
    proof {
        worst_case_formula_lemma(n as nat);
    }
    let n_int = n as i32;
    let intermediate = n_int * (n_int * n_int + 5) / 6;
    let result = intermediate as i8;
    assert(result as int >= 1) by {
        assert(n as int >= 1);
    }
    result
}
// </vc-code>


}

fn main() {}