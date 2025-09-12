// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn max_value(s: Seq<char>) -> int {
    max_value_up_to_index(s, s.len() as int)
}

spec fn max_value_up_to_index(s: Seq<char>, up_to: int) -> int
    recommends 0 <= up_to <= s.len()
{
    if up_to == 0 { 0 }
    else {
        let current_value = current_value_at_index(s, up_to);
        let max_before = max_value_up_to_index(s, up_to - 1);
        if current_value > max_before { current_value } else { max_before }
    }
}

spec fn current_value_at_index(s: Seq<char>, index: int) -> int
    recommends 0 <= index <= s.len()
{
    if index == 0 { 0 }
    else { current_value_at_index(s, index - 1) + (if s[index - 1] == 'I' { 1 } else { -1 }) }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, s: Seq<char>) -> (result: int)
    requires 1 <= n <= 100
    requires n == s.len()
    requires forall|i: int| 0 <= i < s.len() ==> s[i] == 'I' || s[i] == 'D'
    ensures result >= 0
    ensures result == max_value(s)
// </vc-spec>
// <vc-code>
{
    assume(false);
    0int
}
// </vc-code>


}

fn main() {}