// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, k: int) -> bool {
    n >= 1 && k > 0
}

spec fn is_correct_result(n: int, k: int, result: int) -> bool 
    recommends k > 0
{
    result > n && result % k == 0 && forall|x: int| n < x < result ==> #[trigger] (x % k) != 0
}
// </vc-preamble>

// <vc-helpers>
spec fn ceiling_multiple(n: int, k: int) -> int
    recommends k > 0
{
    ((n / k) + 1) * k
}

/* helper modified by LLM (iteration 5): fixed type annotations for literals */
proof fn lemma_ceiling_multiple_properties(n: int, k: int)
    requires k > 0, n >= 1
    ensures
        ceiling_multiple(n, k) > n,
        ceiling_multiple(n, k) % k == 0,
        forall|x: int| n < x < ceiling_multiple(n, k) ==> #[trigger] (x % k) != 0
{
    let result = ceiling_multiple(n, k);
    assert(result == ((n / k) + 1) * k);
    
    // Use fundamental_div property from Verus
    assert(result > n) by {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n, k);
        assert(n == (n / k) * k + (n % k));
        assert(n % k < k);
        assert(n <= (n / k) * k + k - 1);
        assert(result == (n / k) * k + k);
        assert(result > n);
    };
    
    assert(result % k == 0) by {
        vstd::arithmetic::div_mod::lemma_mod_multiples_basic(((n / k) + 1), k);
    };
    
    assert(forall|x: int| n < x < result ==> #[trigger] (x % k) != 0) by {
        assert forall|x: int| n < x < result implies #[trigger] (x % k) != 0 by {
            if x % k == 0 {
                assert(x >= k);
                assert(x >= ((n / k) + 1) * k);
                assert(x >= result);
                assert(false);
            }
        }
    };
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: i8)
    requires valid_input(n as int, k as int)
    ensures is_correct_result(n as int, k as int, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type annotations for integer literals */
    proof {
        lemma_ceiling_multiple_properties(n as int, k as int);
        assert(n as int >= 1 && k as int > 0);
        assert(n / k <= 127i8 / 1i8); // worst case overflow check
        assert((n / k + 1i8) * k <= 128i8); // ensure result fits in i8
    }
    
    let quotient = n / k;
    assert(quotient >= 0i8);
    assert(quotient + 1i8 <= 127i8);
    assert((quotient + 1i8) * k <= 127i8);
    
    let result = (quotient + 1i8) * k;
    
    proof {
        assert(result as int == ceiling_multiple(n as int, k as int));
    }
    
    result
}
// </vc-code>


}

fn main() {}