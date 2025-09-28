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
/* helper modified by LLM (iteration 4): removed incorrect lemma_rounding_bound */
spec fn round_to_nearest_ten(n: int) -> int
    recommends n >= 0
{
    let quotient = n / 10;
    let remainder = n % 10;
    if remainder < 5 {
        quotient * 10
    } else if remainder > 5 {
        (quotient + 1) * 10
    } else {
        if quotient % 2 == 0 {
            quotient * 10
        } else {
            (quotient + 1) * 10
        }
    }
}

/* helper modified by LLM (iteration 3): changed recommends to requires */
proof fn lemma_rounding_satisfies_valid_result(n: int)
    requires n >= 0
    ensures valid_result(n, round_to_nearest_ten(n))
{
    let q = n / 10;
    let r = n % 10;
    assert(r >= 0 && r < 10);
    if r < 5 {
        assert(round_to_nearest_ten(n) == q * 10);
        assert(valid_result(n, q * 10));
    } else if r > 5 {
        assert(round_to_nearest_ten(n) == (q+1)*10);
        assert(valid_result(n, (q+1)*10));
    } else {
        if q % 2 == 0 {
            assert(round_to_nearest_ten(n) == q * 10);
            assert(valid_result(n, q * 10));
        } else {
            assert(round_to_nearest_ten(n) == (q+1)*10);
            assert(valid_result(n, (q+1)*10));
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
/* code modified by LLM (iteration 4): use int arithmetic to prevent overflow */
{
    let n_int = n as int;
    let result_int = round_to_nearest_ten(n_int);
    let result_i8 = result_int as i8;
    
    proof {
        lemma_rounding_satisfies_valid_result(n_int);
        assert(n_int >= 0);
        assert(result_int >= 0);
        assert(result_int % 10 == 0);
        assert(result_int <= 120);
    }
    
    result_i8
}
// </vc-code>


}

fn main() {}