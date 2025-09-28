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
proof fn lemma_count_prefix_extend(s: Seq<char>, k: int, bracket: char)
    requires
        0 <= k < s.len(),
        bracket == '<' || bracket == '>',
        valid_bracket_string(s),
    ensures
        count_brackets_prefix(s, k + 1, bracket) == 
            count_brackets_prefix(s, k, bracket) + (if s[k] == bracket { 1int } else { 0int }),
{
}

proof fn lemma_count_prefix_monotonic(s: Seq<char>, i: int, j: int, bracket: char)
    requires
        0 <= i <= j <= s.len(),
        bracket == '<' || bracket == '>',
        valid_bracket_string(s),
    ensures
        count_brackets_prefix(s, i, bracket) <= count_brackets_prefix(s, j, bracket),
    decreases j - i
{
    if i < j {
        lemma_count_prefix_monotonic(s, i, j - 1, bracket);
        lemma_count_prefix_extend(s, j - 1, bracket);
    }
}

/* helper modified by LLM (iteration 5): fixed balance maintenance lemma logic */
proof fn lemma_balance_maintained(s: Seq<char>, k: int)
    requires
        0 <= k < s.len(),
        valid_bracket_string(s),
        count_brackets_prefix(s, k, '<') >= count_brackets_prefix(s, k, '>'),
    ensures
        count_brackets_prefix(s, k + 1, '<') >= count_brackets_prefix(s, k + 1, '>'),
{
    lemma_count_prefix_extend(s, k, '<');
    lemma_count_prefix_extend(s, k, '>');
    if s[k] == '<' {
        assert(count_brackets_prefix(s, k + 1, '<') == count_brackets_prefix(s, k, '<') + 1);
        assert(count_brackets_prefix(s, k + 1, '>') == count_brackets_prefix(s, k, '>'));
    } else {
        assert(count_brackets_prefix(s, k + 1, '<') == count_brackets_prefix(s, k, '<'));
        assert(count_brackets_prefix(s, k + 1, '>') == count_brackets_prefix(s, k, '>') + 1);
    }
}

/* helper modified by LLM (iteration 5): added lemma for final balance check */
proof fn lemma_balance_zero_implies_nested(s: Seq<char>)
    requires
        valid_bracket_string(s),
        (forall|k: int| 0 <= k <= s.len() ==> count_brackets_prefix(s, k, '<') >= count_brackets_prefix(s, k, '>')),
        count_brackets_prefix(s, s.len() as int, '<') - count_brackets_prefix(s, s.len() as int, '>') == 0,
    ensures
        properly_nested(s),
{
    assert(count_brackets_prefix(s, s.len() as int, '<') == count_brackets_prefix(s, s.len() as int, '>'));
}
// </vc-helpers>

// <vc-spec>
fn correct_bracketing(brackets: Vec<char>) -> (result: bool)
    requires valid_bracket_string(brackets@)
    ensures result <==> properly_nested(brackets@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed balance tracking with proper types and bounds checking */
    let mut balance: int = 0;
    let mut i: usize = 0;
    
    while i < brackets.len()
        invariant
            0 <= i <= brackets.len(),
            valid_bracket_string(brackets@),
            balance == count_brackets_prefix(brackets@, i as int, '<') - count_brackets_prefix(brackets@, i as int, '>'),
            balance >= 0,
            forall|k: int| 0 <= k <= i ==> count_brackets_prefix(brackets@, k, '<') >= count_brackets_prefix(brackets@, k, '>'),
        decreases brackets.len() - i
    {
        proof {
            lemma_count_prefix_extend(brackets@, i as int, '<');
            lemma_count_prefix_extend(brackets@, i as int, '>');
            lemma_balance_maintained(brackets@, i as int);
        }
        
        if brackets[i] == '<' {
            balance = balance + 1;
        } else {
            if balance == 0 {
                return false;
            }
            balance = balance - 1;
        }
        i = i + 1;
    }
    
    proof {
        if balance == 0 {
            lemma_balance_zero_implies_nested(brackets@);
        }
    }
    
    balance == 0
}
// </vc-code>


}

fn main() {}