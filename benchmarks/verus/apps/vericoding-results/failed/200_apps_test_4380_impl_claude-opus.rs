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
/* helper modified by LLM (iteration 5): no changes needed */
proof fn lemma_odd_product_exists(a: int, b: int)
    requires
        valid_input(a, b),
        a != 2,
        b != 2,
    ensures
        exists_odd_product(a, b),
{
    assert(a == 1 || a == 3);
    assert(b == 1 || b == 3);
    assert(is_odd(a * b * 1));
}

proof fn lemma_no_odd_product_when_even(a: int, b: int)
    requires
        valid_input(a, b),
        a == 2 || b == 2,
    ensures
        !exists_odd_product(a, b),
{
    assert forall|c: int| 1 <= c <= 3 implies !is_odd(a * b * c) by {
        if a == 2 {
            assert((2 * b * c) % 2 == 0);
        } else {
            assert((a * 2 * c) % 2 == 0);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (result: Seq<char>)
  requires valid_input(a as int, b as int)
  ensures result == (if should_answer_yes(a as int, b as int) { "Yes"@ } else { "No"@ })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): return Seq<char> directly without seq! macro */
    if a != 2 && b != 2 {
        proof {
            lemma_odd_product_exists(a as int, b as int);
        }
        Seq::new(3, |i: int| if i == 0 { 'Y' } else if i == 1 { 'e' } else { 's' })
    } else {
        proof {
            lemma_no_odd_product_when_even(a as int, b as int);
        }
        Seq::new(2, |i: int| if i == 0 { 'N' } else { 'o' })
    }
}
// </vc-code>


}

fn main() {}