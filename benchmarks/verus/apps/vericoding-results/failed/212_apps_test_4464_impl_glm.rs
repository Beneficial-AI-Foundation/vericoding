// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int, c: int) -> bool {
    1 <= a <= 100 && 1 <= b <= 100 && 0 <= c < b
}

spec fn is_solvable(a: int, b: int, c: int) -> bool {
    exists|i: int| 1 <= i < b && #[trigger] ((i * (a % b)) % b) == c
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed solvability check using proper arithmetic operations */
fn check_solvable_exec(a: i8, b: i8, c: i8) -> bool {
    let mut i: i8 = 1;
    while i < b
        invariant 
            1 <= i <= b,
        decreases (b - i) as int
    {
        let a_mod_b = (a as int) % (b as int);
        let product = (i as int) * a_mod_b;
        let remainder = product % (b as int);
        if remainder == c as int {
            return true;
        }
        i += 1;
    }
    false
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, c: i8) -> (result: String)
    requires 
        valid_input(a as int, b as int, c as int)
    ensures 
        (result@ == "YES"@) <==> is_solvable(a as int, b as int, c as int),
        (result@ == "NO"@) || (result@ == "YES"@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed String creation using sequence literals */
    if check_solvable_exec(a, b, c) {
        let yes_chars = ['Y', 'E', 'S'];
        let s = String::from_iter(yes_chars.iter());
        s
    } else {
        let no_chars = ['N', 'O'];
        let s = String::from_iter(no_chars.iter());
        s
    }
}
// </vc-code>


}

fn main() {}