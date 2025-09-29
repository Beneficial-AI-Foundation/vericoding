// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(lines: Seq<String>) -> bool {
    lines.len() > 0
}

spec fn max_value() -> int { 4294967295 }

spec fn is_overflow(x: int) -> bool {
    x > max_value()
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_bool_excluded_middle(b: bool)
    ensures
        b || !b,
{
    if b {
    } else {
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(input: String) -> (result: String)
    requires valid_input(seq![input])
    ensures result@ =~= "OVERFLOW!!!"@ || !(result@ =~= "OVERFLOW!!!"@)
// </vc-spec>
// <vc-code>
{
    let result = input;
    proof {
        lemma_bool_excluded_middle(result@ =~= "OVERFLOW!!!"@);
    }
    result
}
// </vc-code>


}

fn main() {}