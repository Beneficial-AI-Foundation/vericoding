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
/* helper modified by LLM (iteration 2): fixed lemma syntax */
proof fn lemma_odd_product_existence(a: int, b: int)
    requires
        valid_input(a, b),
        a != 2 && b != 2,
    ensures exists|c: int| 1 <= c <= 3 && is_odd(a * b * c)
{
    if (a * b) % 2 == 1 {
        assert(is_odd(a * b * 1));
        assert(1 <= 1 <= 3);
    } else {
        assert(is_odd(a * b * 3));
        assert(1 <= 3 <= 3);
    }
}

proof fn lemma_even_product_no_odd(a: int, b: int)
    requires
        valid_input(a, b),
        a == 2 || b == 2,
    ensures forall|c: int| 1 <= c <= 3 ==> !is_odd(a * b * c)
{
    assert((a * b) % 2 == 0);
    assert(forall|c: int| 1 <= c <= 3 ==> (a * b * c) % 2 == 0);
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (result: Seq<char>)
  requires valid_input(a as int, b as int)
  ensures result == (if should_answer_yes(a as int, b as int) { "Yes"@ } else { "No"@ })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): implementation using helper lemmas */
    if a != 2 && b != 2 {
        proof {
            lemma_odd_product_existence(a as int, b as int);
        }
        "Yes"@
    } else {
        proof {
            lemma_even_product_no_odd(a as int, b as int);
        }
        "No"@
    }
}
// </vc-code>


}

fn main() {}