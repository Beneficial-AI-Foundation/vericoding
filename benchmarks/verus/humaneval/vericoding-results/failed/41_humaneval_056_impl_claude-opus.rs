// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_brackets_prefix(s: Seq<char>, end: int, bracket: char) -> int
    decreases end
{
    if end == 0 {
        0
    } else if 0 <= end <= s.len() && (bracket == '<' || bracket == '>') && s[end - 1] == bracket {
        1 + count_brackets_prefix(s, end - 1, bracket)
    } else if 0 <= end <= s.len() && (bracket == '<' || bracket == '>') {
        count_brackets_prefix(s, end - 1, bracket)
    } else {
        0
    }
}

spec fn valid_bracket_string(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] == '<' || s[i] == '>'
}

spec fn properly_nested(brackets: Seq<char>) -> bool {
    valid_bracket_string(brackets) &&
    (forall|k: int| 0 <= k <= brackets.len() ==> 
        count_brackets_prefix(brackets, k, '<') >= count_brackets_prefix(brackets, k, '>')) &&
    count_brackets_prefix(brackets, brackets.len() as int, '<') == count_brackets_prefix(brackets, brackets.len() as int, '>')
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn correct_bracketing(brackets: Vec<char>) -> (result: bool)
    requires valid_bracket_string(brackets@)
    ensures result <==> properly_nested(brackets@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed integer literal types for int operations */
    let mut depth: int = 0int;
    let mut i: usize = 0;
    
    while i < brackets.len()
        invariant
            0 <= i <= brackets.len(),
            valid_bracket_string(brackets@),
            depth == count_brackets_prefix(brackets@, i as int, '<') - count_brackets_prefix(brackets@, i as int, '>'),
            depth >= 0int,
            forall|k: int| 0 <= k <= i ==> count_brackets_prefix(brackets@, k, '<') >= count_brackets_prefix(brackets@, k, '>'),
        decreases brackets.len() - i
    {
        if brackets[i] == '<' {
            depth = depth + 1int;
        } else {
            if depth == 0int {
                return false;
            }
            depth = depth - 1int;
        }
        i = i + 1;
    }
    
    depth == 0int
}
// </vc-code>


}

fn main() {}