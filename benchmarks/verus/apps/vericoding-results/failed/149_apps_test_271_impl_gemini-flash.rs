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
{
  let n_int: int = n as int;

  let quotient = n_int / 10;
  let remainder = n_int % 10;
  let result_int: int;

  if remainder < 5 {
    result_int = quotient * 10;
  } else if remainder > 5 {
    result_int = (quotient + 1) * 10;
  } else { /* remainder == 5 */
    if quotient % 2 == 0 {
      result_int = quotient * 10;
    } else {
      result_int = (quotient + 1) * 10;
    }
  }
  result_int as i8
}
// </vc-code>


}

fn main() {}