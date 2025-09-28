// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(d: int) -> bool {
    22 <= d <= 25
}

spec fn expected_output(d: int) -> Seq<char> {
    if valid_input(d) {
        let eve_count = 25 - d;
        let base_string = seq!['C', 'h', 'r', 'i', 's', 't', 'm', 'a', 's'];
        if eve_count == 0 {
            base_string
        } else {
            base_string + repeat_eve(eve_count)
        }
    } else {
        seq![]
    }
}

spec fn repeat_eve(count: int) -> Seq<char>
    decreases count
{
    if count <= 0 {
        seq![]
    } else {
        seq![' ', 'E', 'v', 'e'] + repeat_eve(count - 1)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): used old(s) in requires clause to fix compilation error */
fn append_eves(s: &mut String, count: i8)
    requires
        0 <= count,
        old(s).is_ascii(),
    ensures
        s@ == old(s)@ + repeat_eve(count as int),
        s.is_ascii(),
{
    let mut i: i8 = 0;
    while i < count
        invariant
            0 <= i <= count,
            s.is_ascii(),
            s@ + repeat_eve((count - i) as int) == old(s)@ + repeat_eve(count as int),
        decreases count - i
    {
        s.push(' ');
        s.push('E');
        s.push('v');
        s.push('e');
        i = i + 1;
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(d: i8) -> (result: String)
    requires valid_input(d as int)
    ensures result@ == expected_output(d as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): no changes required; fix was in helper */
    let mut result = String::from_str("Christmas");
    let eve_count = 25 - d;
    append_eves(&mut result, eve_count);
    result
}

// </vc-code>


}

fn main() {}