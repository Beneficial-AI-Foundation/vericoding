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
/* helper modified by LLM (iteration 5): use String::from to avoid collect issue */
exec fn bool_to_string(b: bool) -> (s: String)
    ensures s@ == (if b { seq!['Y','E','S'] } else { seq!['N','O'] })
{
    let s: String = if b {
        String::from("YES")
    } else {
        String::from("NO")
    };
    s
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, x: i8) -> (result: String)
    requires valid_input(a as int, b as int, x as int)
    ensures result@ =~= seq!['Y', 'E', 'S'] <==> can_have_exactly_cats(a as int, b as int, x as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed helper call, no change needed */
    let a_val = a as i32;
    let b_val = b as i32;
    let x_val = x as i32;
    let cond = (a_val <= x_val) && (x_val <= a_val + b_val);
    bool_to_string(cond)
}
// </vc-code>


}

fn main() {}