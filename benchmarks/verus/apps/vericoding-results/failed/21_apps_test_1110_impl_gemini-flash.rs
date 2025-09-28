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
/* helper modified by LLM (iteration 4): Removed unnecessary helper function and fixed compilation error for ghost mut variable */

// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures result as int == worst_case_presses(n as int) && result as int >= 1
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Corrected compilation error: `ghost mut` variable cannot be defined in a function body; moved the result calculation out of the proof block and into the main function body to enable it to be returned. */
{
    let n_int = n as int;
    let result_int: int = n_int * (n_int * n_int + 5) / 6;

    proof {
        assert(result_int == worst_case_presses(n_int));
        assert(result_int >= 1) by {
            if (n_int == 0) {
                assert(false);
            } else {
                assert(n_int >= 1);
                assert(n_int * n_int >= 1);
                assert(n_int * n_int + 5 >= 6);
                assert( (n_int * (n_int * n_int + 5)) >= 0);
                assert( (n_int * (n_int * n_int + 5)) / 6 >= 1) by {
                    if (n_int == 1) {
                        assert(1 * (1*1 + 5) / 6 == 1);
                    } else if (n_int == 2) {
                        assert(2 * (2*2 + 5) / 6 == 3);
                    } else if (n_int == 3) {
                        assert(3 * (3*3 + 5) / 6 == 7);
                    }
                }
            }
        }
    }

    result_int as i8
}
// </vc-code>


}

fn main() {}