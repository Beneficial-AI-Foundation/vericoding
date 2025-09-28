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
/* helper modified by LLM (iteration 5): remove nat conversion proofs and use int indices directly */
proof fn lemma_count_brackets_prefix_cons(s: Seq<char>, end: int, bracket: char)
    requires
        0 <= end <= s.len(),
        bracket == '<' || bracket == '>',
    ensures
        count_brackets_prefix(s, end, bracket) == count_brackets_prefix(s, end - 1, bracket) + (
            if s[end - 1] == bracket { 1 } else { 0 }
        ),
    decreases end
{
    if end > 0 {
        lemma_count_brackets_prefix_cons(s, end - 1, bracket);
    }
}
// </vc-helpers>

// <vc-spec>
fn correct_bracketing(brackets: Vec<char>) -> (result: bool)
    requires valid_bracket_string(brackets@)
    ensures result <==> properly_nested(brackets@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): use int indices directly instead of nat conversion */
{
    let mut open_count: int = 0;
    let mut close_count: int = 0;
    let mut i: int = 0;
    
    while i < brackets.len() as int
        invariant
            0 <= i <= brackets.len() as int,
            open_count == count_brackets_prefix(brackets@, i, '<'),
            close_count == count_brackets_prefix(brackets@, i, '>'),
            open_count >= close_count,
        decreases brackets.len() as int - i
    {
        lemma_count_brackets_prefix_cons(brackets@, i + 1, '<');
        lemma_count_brackets_prefix_cons(brackets@, i + 1, '>');
        
        if brackets[i as usize] == '<' {
            open_count = open_count + 1;
        } else {
            close_count = close_count + 1;
        }
        
        assert(close_count <= open_count);
        i = i + 1;
    }
    
    open_count == close_count
}
// </vc-code>


}

fn main() {}