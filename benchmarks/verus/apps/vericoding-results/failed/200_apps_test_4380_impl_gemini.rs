// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int) -> bool {
    1 <= a <= 3 && 1 <= b <= 3
}

spec fn is_odd(n: int) -> bool {
    n % 2 == 1
}

spec fn exists_odd_product(a: int, b: int) -> bool {
    valid_input(a, b) ==> exists|c: int| 1 <= c <= 3 && #[trigger] is_odd(a * b * c)
}

spec fn should_answer_yes(a: int, b: int) -> bool {
    valid_input(a, b) ==> (a != 2 && b != 2)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): fixed compilation error by using the correct lemma mul_is_odd */
proof fn lemma_odd_product_iff_yes(a: int, b: int)
    requires
        valid_input(a, b),
    ensures
        is_odd(a * b) <==> should_answer_yes(a, b),
{
    assert forall |n: int| 1 <= n <= 3 implies (is_odd(n) <==> (n != 2)) by {
        if n == 1 {
            assert(is_odd(1) && 1 != 2);
        } else if n == 2 {
            assert(!is_odd(2) && !(2 != 2));
        } else {
            assert(n == 3);
            assert(is_odd(3) && 3 != 2);
        }
    };

    vstd::arithmetic::mul_div_mod_properties::mul_is_odd(a, b);
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (result: Seq<char>)
  requires valid_input(a as int, b as int)
  ensures result == (if should_answer_yes(a as int, b as int) { "Yes"@ } else { "No"@ })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): retaining correct implementation from previous turn */
    if a != 2 && b != 2 {
        "Yes"@
    } else {
        "No"@
    }
}
// </vc-code>


}

fn main() {}