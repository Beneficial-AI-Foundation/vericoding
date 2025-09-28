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
/* helper modified by LLM (iteration 5): Removed unused helper: `lemma_count_brackets_prefix_nondecreasing`. */
proof fn lemma_char_at_pos(brackets: Vec<char>, i: int)
    requires
        0 <= i < brackets.len(),
    ensures
        brackets@[i] == brackets.spec_index(i as int)
{
    // This lemma simply states the relationship between Seq and Vec indexing,
    // which Verus often handles implicitly.
}
// </vc-helpers>

// <vc-spec>
fn correct_bracketing(brackets: Vec<char>) -> (result: bool)
    requires valid_bracket_string(brackets@)
    ensures result <==> properly_nested(brackets@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed integer literal types to match `vstd::prelude::int` where necessary using `0.into()`, `1.into()` etc. And fixed `brackets[i]` to `brackets.index(i)` and `brackets.spec_index(i as int)` */
{
    let mut balance: int = 0.into();
    let mut i: usize = 0;

    while i < brackets.len()
        invariant
            0 <= i as int <= brackets.len() as int,
            balance == count_brackets_prefix(brackets@, i as int, '<') - count_brackets_prefix(brackets@, i as int, '>'),
            0.into() <= balance,
            valid_bracket_string(brackets@),
            forall|k: int| 0 <= k <= i as int ==> count_brackets_prefix(brackets@, k, '<') >= count_brackets_prefix(brackets@, k, '>'),
        decreases brackets.len() - i
    {
        proof {
            lemma_char_at_pos(brackets, i as int);
        }
        
        let char_at_i = brackets.index(i);
        if char_at_i == '<' {
            balance = balance + 1.into();
        } else {
            balance = balance - 1.into();
        }

        if balance < 0.into() {
            // If balance ever drops below zero, it means we have more 'override' brackets than 'open' brackets
            return false;
        }
        
        i = i + 1;
    }

    // After the loop, check if the final balance is zero
    // This ensures that all 'open' brackets have been 'closed'
    balance == 0.into()
}
// </vc-code>


}

fn main() {}