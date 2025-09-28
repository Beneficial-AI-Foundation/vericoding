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
/* helper modified by LLM (iteration 5): build YES using String::new and push to avoid unsupported String::from */
fn mk_yes() -> (s: String)
    ensures s@ =~= seq!['Y', 'E', 'S'],
{
    let mut s = String::new();
    s.push('Y');
    s.push('E');
    s.push('S');
    s
}

/* helper modified by LLM (iteration 5): build NO using String::new and push to avoid unsupported String::from */
fn mk_no() -> (s: String)
    ensures s@ =~= seq!['N', 'O'],
{
    let mut s = String::new();
    s.push('N');
    s.push('O');
    s
}

fn can_have(a: i8, b: i8, x: i8) -> (r: bool)
    requires
        valid_input(a as int, b as int, x as int),
    ensures
        r <==> can_have_exactly_cats(a as int, b as int, x as int),
{
    let ai: i16 = a as i16;
    let bi: i16 = b as i16;
    let xi: i16 = x as i16;
    let sum: i16 = ai + bi;
    let cond = ai <= xi && xi <= sum;
    proof {
        assert(ai as int == a as int);
        assert(bi as int == b as int);
        assert(xi as int == x as int);
        assert(sum as int == ai as int + bi as int);
        assert(cond <==> (ai as int <= xi as int && xi as int <= sum as int));
        assert(cond <==> (a as int <= x as int && x as int <= a as int + b as int));
    }
    cond
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, x: i8) -> (result: String)
    requires valid_input(a as int, b as int, x as int)
    ensures result@ =~= seq!['Y', 'E', 'S'] <==> can_have_exactly_cats(a as int, b as int, x as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): branch on feasibility and construct YES/NO via push-based helpers */
    let r = can_have(a, b, x);
    if r {
        mk_yes()
    } else {
        mk_no()
    }
}
// </vc-code>


}

fn main() {}