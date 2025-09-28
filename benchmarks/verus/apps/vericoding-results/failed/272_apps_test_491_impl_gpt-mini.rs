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
/* helper modified by LLM (iteration 5): prove max_balance result fits in i8 range */
proof fn result_fits_i8(n: i8)
    requires valid_input(n as int)
    ensures
        max_balance_after_operation(n as int) >= (i8::MIN as int),
        max_balance_after_operation(n as int) <= (i8::MAX as int),
{
    let ni = n as int;
    if ni >= 0 {
        // For non-negative n the function is identity
        assert(max_balance_after_operation(ni) == ni);
        assert(ni >= (i8::MIN as int));
        assert(ni <= (i8::MAX as int));
    } else {
        // For negative n we analyze the two options
        let opt1 = ni / 10;
        let a = ni / 100;
        let b = ni % 10;
        let opt2 = a * 10 + b;

        // opt1 is a quotient by 10 so its magnitude is no greater than |n| and thus within i8 range
        assert(opt1 >= (i8::MIN as int));
        assert(opt1 <= (i8::MAX as int));

        // Bound a and b for n in i8 range: a = n/100 in [-2,1] (safe), b = n%10 in [-9,9]
        assert(a >= -2);
        assert(a <= 1);
        assert(b >= -9);
        assert(b <= 9);

        // opt2 = a*10 + b lies in a small interval (here within i8 bounds)
        assert(opt2 >= (i8::MIN as int));
        assert(opt2 <= (i8::MAX as int));

        if opt1 > opt2 {
            assert(max_balance_after_operation(ni) == opt1);
        } else {
            assert(max_balance_after_operation(ni) == opt2);
        }

        assert(max_balance_after_operation(ni) >= (i8::MIN as int));
        assert(max_balance_after_operation(ni) <= (i8::MAX as int));
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures result as int == max_balance_after_operation(n as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute using int arithmetic and cast with lemma ensuring bounds */
    let n_int = n as int;
    let m_int = max_balance_after_operation(n_int);
    proof {
        result_fits_i8(n);
        assert(m_int >= (i8::MIN as int));
        assert(m_int <= (i8::MAX as int));
    }
    m_int as i8
}
// </vc-code>


}

fn main() {}