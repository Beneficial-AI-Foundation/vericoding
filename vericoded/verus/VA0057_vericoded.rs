// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int, f: int, k: int) -> bool {
  a > 0 && b > 0 && f > 0 && k > 0 && f < a
}

spec fn impossible_conditions(a: int, b: int, f: int, k: int) -> bool {
  b < f ||                                    
  b < a - f ||                               
  (k > 1 && b < 2 * a - f) ||               
  (k == 1 && b < a && b < f)                
}

spec fn feasibility_conditions(a: int, b: int, f: int, k: int) -> bool {
  b >= f &&                                  
  b >= a - f &&                             
  (k <= 1 || b >= 2 * a - f) &&            
  (k == 1 ==> (b >= a || b >= f))          
}

spec fn single_journey_result(a: int, b: int, f: int, k: int, result: int) -> bool {
  k == 1 && result >= 0 ==> (
    (b >= a && result == 0) ||                
    (b < a && b >= f && result == 1)          
  )
}

spec fn multi_journey_feasibility(a: int, b: int, f: int, k: int, result: int) -> bool {
  k > 1 && result >= 0 ==> (
    b >= f && b >= a - f && b >= 2 * a - f    
  )
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, f: i8, k: i8) -> (result: i8)
  requires
    valid_input(a as int, b as int, f as int, k as int)
  ensures
    result as int >= -1 &&
    ((result as int == -1) <==> impossible_conditions(a as int, b as int, f as int, k as int)) &&
    (result as int >= 0 ==> result as int <= k as int) &&
    (result as int >= 0 ==> feasibility_conditions(a as int, b as int, f as int, k as int)) &&
    single_journey_result(a as int, b as int, f as int, k as int, result as int) &&
    multi_journey_feasibility(a as int, b as int, f as int, k as int, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): fix compilation error by breaking down expressions in proof block */
    let a_wide = a as i32;
    let b_wide = b as i32;
    let f_wide = f as i32;
    let k_wide = k as i32;

    let cond1 = b_wide < f_wide;
    let cond2 = b_wide < a_wide - f_wide;
    let cond3 = (k_wide > 1) && (b_wide < 2 * a_wide - f_wide);
    let cond4 = (k_wide == 1) && (b_wide < a_wide) && (b_wide < f_wide);

    let impossible = cond1 || cond2 || cond3 || cond4;

    proof {
        let a_int = a as int;
        let b_int = b as int;
        let f_int = f as int;
        let k_int = k as int;

        assert(cond1 == (b_int < f_int));
        assert(cond2 == (b_int < a_int - f_int));
        assert(cond3 == ((k_int > 1) && (b_int < 2 * a_int - f_int)));
        assert(cond4 == ((k_int == 1) && (b_int < a_int) && (b_int < f_int)));
        assert(impossible == impossible_conditions(a_int, b_int, f_int, k_int));
    }

    if impossible {
        -1
    } else if b_wide >= a_wide {
        0
    } else {
        1
    }
}
// </vc-code>


}

fn main() {}