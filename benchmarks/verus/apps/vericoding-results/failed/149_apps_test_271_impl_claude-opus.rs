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
    /* code modified by LLM (iteration 5): Implement banker's rounding without verification bypasses */
    let quotient = n / 10;
    let remainder = n % 10;
    
    assert(0 <= quotient <= 12) by {
        assert(n >= 0);
        assert(n <= 127);  // i8 max value
    }
    assert(0 <= remainder <= 9);
    
    if remainder < 5 {
        let result = quotient * 10;
        assert(result >= 0);
        assert(result <= 120);
        assert(result % 10 == 0);
        assert(valid_result(n as int, result as int));
        result
    } else if remainder > 5 {
        // Round up: (quotient + 1) * 10
        // Need to check for overflow
        if quotient >= 12 {
            // For n >= 126 with remainder > 5, result would be >= 130
            // Since i8 max is 127, we return 120 as the closest valid value
            let result = 120i8;
            // Note: This violates the spec for n=126,127 with remainder > 5
            // but there's no valid i8 value that satisfies it
            result
        } else {
            let result = (quotient + 1) * 10;
            assert(result >= 10);
            assert(result <= 120) by {
                assert(quotient <= 11);
            }
            assert(result % 10 == 0);
            assert(valid_result(n as int, result as int));
            result
        }
    } else {
        // remainder == 5, banker's rounding
        assert(remainder == 5);
        if quotient % 2 == 0 {
            // Round down to nearest even (quotient is already even)
            let result = quotient * 10;
            assert(result >= 0);
            assert(result <= 120);
            assert(result % 10 == 0);
            assert(valid_result(n as int, result as int));
            result
        } else {
            // Round up to nearest even (quotient + 1 will be even)
            assert(quotient % 2 == 1);
            if quotient >= 12 {
                // quotient can't be both >= 12 and odd, since 12 is even
                // This case is actually impossible
                assert(false) by {
                    assert(quotient == 12);
                    assert(12 % 2 == 0);
                    assert(quotient % 2 == 1);
                }
                unreached()
            } else {
                let result = (quotient + 1) * 10;
                assert(result >= 10);
                assert(result <= 120) by {
                    assert(quotient <= 11);
                }
                assert(result % 10 == 0);
                assert(valid_result(n as int, result as int));
                result
            }
        }
    }
}
// </vc-code>


}

fn main() {}