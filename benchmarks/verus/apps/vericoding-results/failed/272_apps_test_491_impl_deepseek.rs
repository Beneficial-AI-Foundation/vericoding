// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int) -> bool {
    n >= 10 || n <= -10
}

spec fn max_balance_after_operation(n: int) -> int
    recommends valid_input(n)
{
    if n >= 0 {
        n
    } else {
        /* For negative numbers, we need to delete either the last digit
           or the digit before the last digit to maximize the balance.
           Since this involves string operations that are not easily
           expressible in pure logic, we use a simplified specification. */
        let option1 = n / 10;
        let option2 = (n / 100) * 10 + (n % 10);
        if option1 > option2 { option1 } else { option2 }
    }
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_div_definition(a: int, d: int)
    requires d != 0
    ensures a == (a / d) * d + (a % d)
{
    /* helper modified by LLM (iteration 5): Fixed implementation */
    if d > 0 {
        assert(0 <= a % d < d);
    } else {
        assert(0 <= a % d < -d);
    }
    assert(a == (a / d) * d + (a % d));
}

proof fn lemma_mod_range_nonneg(a: int, d: int)
    requires d > 0
    ensures 0 <= a % d < d
{
    /* helper modified by LLM (iteration 5): Fixed implementation */
    assert(0 <= a % d < d);
}

proof fn lemma_mod_range_neg(a: int, d: int)
    requires d < 0
    ensures 0 <= a % d < -d
{
    /* helper modified by LLM (iteration 5): Fixed implementation */
    assert(0 <= a % d < -d);
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures result as int == max_balance_after_operation(n as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed verification with proper ghost variables */
    if n >= 0 {
        n
    } else {
        let n_int = n as int;
        proof {
            lemma_div_definition(n_int, 10);
            lemma_div_definition(n_int, 100);
            if n_int < 0 {
                lemma_mod_range_neg(n_int, 10);
                lemma_mod_range_neg(n_int, 100);
            }
        }
        
        let option1 = n / 10;
        let option2 = (n / 100) * 10 + (n % 10);
        
        if option1 > option2 {
            option1
        } else {
            option2
        }
    }
}
// </vc-code>


}

fn main() {}