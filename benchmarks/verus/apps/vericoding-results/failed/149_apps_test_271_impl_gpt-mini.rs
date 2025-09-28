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
spec fn round_nearest10(n: int) -> int
    requires n >= 0
    ensures valid_result(n, result)
{
    let q = n / 10;
    let r = n % 10;
    if r < 5 {
        q * 10
    } else if r > 5 {
        (q + 1) * 10
    } else {
        if q % 2 == 0 { q * 10 } else { (q + 1) * 10 }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
  requires n >= 0
  ensures valid_result(n as int, result as int)
// </vc-spec>
// <vc-code>
{
    let n_int = n as int;
    let q = n_int / 10;
    let r = n_int % 10;
    let result_int = if r < 5 {
        q * 10
    } else if r > 5 {
        (q + 1) * 10
    } else {
        if q % 2 == 0 { q * 10 } else { (q + 1) * 10 }
    };
    let result = result_int as i8;
    result
}
// </vc-code>


}

fn main() {}