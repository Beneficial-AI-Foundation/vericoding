// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_result(n: int, result: int) -> bool
  recommends n >= 0
{
  let quotient = n / 10;
  let remainder = n % 10;
  result % 10 == 0 && 
  result >= 0 &&
  (remainder < 5 ==> result == quotient * 10) &&
  (remainder > 5 ==> result == (quotient + 1) * 10) &&
  (remainder == 5 ==> (quotient % 2 == 0 ==> result == quotient * 10) && 
                      (quotient % 2 == 1 ==> result == (quotient + 1) * 10))
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
  requires n >= 0
  ensures valid_result(n as int, result as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed compilation errors by using i64 instead of int for calculations, removed verification bypass assume statement */
{
    let quotient = (n as i64) / 10;
    let remainder = (n as i64) % 10;
    let result_i64 = if remainder < 5 {
        quotient * 10
    } else if remainder > 5 {
        (quotient + 1) * 10
    } else {
        if quotient % 2 == 0 {
            quotient * 10
        } else {
            (quotient + 1) * 10
        }
    };
    result_i64 as i8
}
// </vc-code>


}

fn main() {}