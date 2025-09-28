// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, a: int) -> bool {
    1 <= n <= 10000 && 0 <= a <= 1000
}

spec fn can_pay_exactly(n: int, a: int) -> bool {
    n % 500 <= a
}

spec fn valid_output(result: String) -> bool {
    result@ == "Yes"@ || result@ == "No"@
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): establish basic i8-to-int bounds used in proofs */
proof fn lemma_i8_bounds(x: i8)
    ensures
        (x as int) <= 127,
        -128 <= (x as int),
{
    assert((x as int) <= 127);
    assert(-128 <= (x as int));
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: i8) -> (result: String)
    requires 
        valid_input(n as int, a as int)
    ensures 
        valid_output(result) &&
        ((result@ == "Yes"@) <==> can_pay_exactly(n as int, a as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): decide by comparing n and a; prove equivalence using 0 <= n < 500 so n % 500 == n */
    let yes: bool = n <= a;
    if yes {
        let result = String::from_str("Yes");
        proof {
            // From precondition
            assert(1 <= (n as int));
            assert(0 <= (a as int));
            // Bounds to relate modulo
            lemma_i8_bounds(n);
            assert((n as int) <= 127);
            assert((n as int) < 500);
            assert(0 <= (n as int));
            assert(0 < 500);
            // Modulo simplifies since 0 <= n < 500
            assert((n as int) % 500 == (n as int));
            // Order preserved by casts
            assert((n as int) <= (a as int)) by { assert(n <= a); };
            // Conclude can_pay_exactly
            assert(can_pay_exactly(n as int, a as int));
        }
        result
    } else {
        let result = String::from_str("No");
        proof {
            assert(1 <= (n as int));
            assert(0 <= (a as int));
            lemma_i8_bounds(n);
            assert((n as int) <= 127);
            assert((n as int) < 500);
            assert(0 <= (n as int));
            assert(0 < 500);
            assert((n as int) % 500 == (n as int));
            assert((n as int) > (a as int)) by { assert(!(n <= a)); };
            assert(!can_pay_exactly(n as int, a as int));
        }
        result
    }
}
// </vc-code>


}

fn main() {}