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
/* helper modified by LLM (iteration 5): prove equivalence of should_answer_yes with concrete condition under valid_input */
proof fn lemma_should_answer_equiv(a: int, b: int)
    requires
        valid_input(a, b),
    ensures
        should_answer_yes(a, b) == (a != 2 && b != 2),
{
    assert(should_answer_yes(a, b) == (valid_input(a, b) ==> (a != 2 && b != 2)));
    assert(valid_input(a, b));
    assert((valid_input(a, b) ==> (a != 2 && b != 2)) == (a != 2 && b != 2));
}

/* helper modified by LLM (iteration 5): relate i8 equality with int equality for constant 2 */
proof fn lemma_i8_cast_eq_2(a: i8)
    ensures
        ((a as int) == 2) == (a == 2i8),
        ((a as int) != 2) == (a != 2i8),
{
    assert((2i8 as int) == 2);
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (result: Seq<char>)
  requires valid_input(a as int, b as int)
  ensures result == (if should_answer_yes(a as int, b as int) { "Yes"@ } else { "No"@ })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): assign result in exec; proofs only for equivalence to spec condition */
    let cond = (a != 2i8) && (b != 2i8);
    proof {
        lemma_should_answer_equiv(a as int, b as int);
        lemma_i8_cast_eq_2(a);
        lemma_i8_cast_eq_2(b);
        assert(should_answer_yes(a as int, b as int) == ((((a as int) != 2) && ((b as int) != 2))));
        assert(((a as int) != 2) == (a != 2i8));
        assert(((b as int) != 2) == (b != 2i8));
        assert(should_answer_yes(a as int, b as int) == cond);
    }
    if cond {
        "Yes"@
    } else {
        "No"@
    }
}
// </vc-code>


}

fn main() {}