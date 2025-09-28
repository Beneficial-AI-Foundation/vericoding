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
proof fn rounding_proof(n: int, result: int)
    requires
        n >= 0,
        result % 10 == 0,
        result >= 0,
    ensures
        valid_result(n, result)
{
    let quotient = n / 10;
    let remainder = n % 10;
    assert(valid_result(n, result) by  {
        assert(result % 10 == 0);
        assert(result >= 0);
        assert(remainder < 5 ==> result == quotient * 10);
        assert(remainder > 5 ==> result == (quotient + 1) * 10);
        assert(remainder == 5 ==> (quotient % 2 == 0 ==> result == quotient * 10) && 
                                 (quotient % 2 == 1 ==> result == (quotient + 1) * 10));
    });
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
  requires n >= 0
  ensures valid_result(n as int, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed invalid let expressions in proof block by separating computation and proof */
    let quotient = n / 10;
    let remainder = n % 10;
    let result_val: i8 = if remainder < 5 {
        quotient * 10
    } else if remainder > 5 {
        (quotient + 1) * 10
    } else {
        if quotient % 2 == 0 {
            quotient * 10
        } else {
            (quotient + 1) * 10
        }
    } as i8;
    
    proof {
        let n_int: int = n as int;
        let result_int: int = result_val as int;
        rounding_proof(n_int, result_int);
    }
    result_val
}
// </vc-code>


}

fn main() {}