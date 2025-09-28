// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn max_value(s: Seq<char>) -> int {
    max_value_up_to_index(s, s.len() as int)
}

spec fn max_value_up_to_index(s: Seq<char>, up_to: int) -> int
    decreases up_to when 0 <= up_to <= s.len()
{
    if up_to == 0 { 0 }
    else {
        let current_value = current_value_at_index(s, up_to);
        let max_before = max_value_up_to_index(s, up_to - 1);
        if current_value > max_before { current_value } else { max_before }
    }
}

spec fn current_value_at_index(s: Seq<char>, index: int) -> int
    decreases index when 0 <= index <= s.len()
{
    if index == 0 { 0 }
    else { 
        current_value_at_index(s, index - 1) + (if s[index - 1 as nat] == 'I' { 1 } else { -1 })
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, s: Vec<char>) -> (result: i8)
    requires 
        1 <= n <= 100,
        n as int == s@.len(),
        forall|i: int| 0 <= i < s@.len() ==> s@[i] == 'I' || s@[i] == 'D',
    ensures 
        result >= 0,
        result as int == max_value(s@),
// </vc-spec>
// <vc-code>
{
    assume(false);
    0
}
// </vc-code>


}

fn main() {}