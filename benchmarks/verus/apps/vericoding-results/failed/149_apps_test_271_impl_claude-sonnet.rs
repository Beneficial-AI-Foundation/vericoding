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
/* helper modified by LLM (iteration 5): added overflow bounds lemma and strengthened verification */

proof fn lemma_quotient_bounds(n: i8)
    requires n >= 0
    ensures (n / 10) <= 12
{
    assert(n <= 127);
    assert(n / 10 <= 127int / 10);
    assert(127int / 10 == 12int);
}

proof fn lemma_no_overflow(n: i8, quotient: i8)
    requires
        n >= 0,
        quotient == n / 10,
        quotient <= 12
    ensures
        quotient * 10 <= 120,
        (quotient + 1) * 10 <= 130,
        quotient * 10 >= 0,
        (quotient + 1) * 10 >= 0
{
    assert(quotient <= 12);
    assert(quotient * 10 <= 12 * 10);
    assert(12 * 10 == 120);
    assert((quotient + 1) <= 13);
    assert((quotient + 1) * 10 <= 13 * 10);
    assert(13 * 10 == 130);
    assert(quotient >= 0);
    assert(quotient * 10 >= 0);
    assert((quotient + 1) >= 1);
    assert((quotient + 1) * 10 >= 10);
}

proof fn lemma_valid_result_properties(n: i8, quotient: i8, remainder: i8, result: i8)
    requires
        n >= 0,
        quotient == n / 10,
        remainder == n % 10,
        quotient <= 12,
        result == if remainder < 5 { quotient * 10 }
                  else if remainder > 5 { (quotient + 1) * 10 }
                  else if quotient % 2 == 0 { quotient * 10 }
                  else { (quotient + 1) * 10 }
    ensures valid_result(n as int, result as int)
{
    lemma_no_overflow(n, quotient);
    
    assert(quotient == (n as int) / 10);
    assert(remainder == (n as int) % 10);
    
    if remainder < 5 {
        assert(result == quotient * 10);
        assert(result as int == (quotient as int) * 10);
    } else if remainder > 5 {
        assert(result == (quotient + 1) * 10);
        assert(result as int == ((quotient as int) + 1) * 10);
    } else {
        assert(remainder == 5);
        if quotient % 2 == 0 {
            assert(result == quotient * 10);
            assert(result as int == (quotient as int) * 10);
        } else {
            assert(result == (quotient + 1) * 10);
            assert(result as int == ((quotient as int) + 1) * 10);
        }
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
    /* code modified by LLM (iteration 5): added bounds assertion before overflow operations */
    let quotient = n / 10;
    let remainder = n % 10;
    
    proof {
        lemma_quotient_bounds(n);
        assert(quotient <= 12);
    }
    
    let result = if remainder < 5 {
        quotient * 10
    } else if remainder > 5 {
        assert(quotient <= 12) by {
            lemma_quotient_bounds(n);
        };
        (quotient + 1) * 10
    } else {
        if quotient % 2 == 0 {
            quotient * 10
        } else {
            assert(quotient <= 12) by {
                lemma_quotient_bounds(n);
            };
            (quotient + 1) * 10
        }
    };
    
    proof {
        lemma_valid_result_properties(n, quotient, remainder, result);
    }
    
    result
}
// </vc-code>


}

fn main() {}