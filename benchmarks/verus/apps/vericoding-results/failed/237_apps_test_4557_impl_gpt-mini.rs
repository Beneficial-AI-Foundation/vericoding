// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int, x: int) -> bool {
    1 <= a <= 100 && 1 <= b <= 100 && 1 <= x <= 200
}

spec fn can_have_exactly_cats(a: int, b: int, x: int) -> bool {
    a <= x <= a + b
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): equate predicate to inequalities */
proof fn lemma_can_have_exactly_cats_equiv(a: int, b: int, x: int)
    ensures
        can_have_exactly_cats(a, b, x) <==> (a <= x && x <= a + b),
{
    assert(can_have_exactly_cats(a, b, x) <==> (a <= x && x <= a + b));
}

// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, x: i8) -> (result: String)
    requires valid_input(a as int, b as int, x as int)
    ensures result@ =~= seq!['Y', 'E', 'S'] <==> can_have_exactly_cats(a as int, b as int, x as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): return "YES" when a <= x <= a + b */
    let ai: int = a as int;
    let bi: int = b as int;
    let xi: int = x as int;
    let cond: bool = ai <= xi && xi <= ai + bi;
    let result: String = if cond {
        String::from("YES")
    } else {
        String::from("NO")
    };
    proof {
        lemma_can_have_exactly_cats_equiv(ai, bi, xi);
        assert((ai <= xi && xi <= ai + bi) == cond);
        if cond {
            assert(result@ =~= seq!['Y','E','S']);
        } else {
            assert(!(result@ =~= seq!['Y','E','S']));
        }
        assert(result@ =~= seq!['Y','E','S'] <==> can_have_exactly_cats(ai, bi, xi));
    }
    result
}

// </vc-code>


}

fn main() {}