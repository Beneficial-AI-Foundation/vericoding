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
fn solve(a: int, b: int, f: int, k: int) -> (result: int)
  requires
    valid_input(a, b, f, k)
  ensures
    result >= -1 &&
    ((result == -1) <==> impossible_conditions(a, b, f, k)) &&
    (result >= 0 ==> result <= k) &&
    (result >= 0 ==> feasibility_conditions(a, b, f, k)) &&
    single_journey_result(a, b, f, k, result) &&
    multi_journey_feasibility(a, b, f, k, result)
// </vc-spec>
// <vc-code>
{
  assume(false);
  unreached()
}
// </vc-code>


}

fn main() {}