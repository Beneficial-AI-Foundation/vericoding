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
/* helper modified by LLM (iteration 2): fixed compilation error */
#[verifier::spinoff_prover]
proof fn lemma_count_prefix_increment(s: Seq<char>, i: int, bracket: char)
    requires
        0 <= i < s.len(),
        bracket == '<' || bracket == '>',
    ensures
        count_brackets_prefix(s, i + 1, bracket) ==
            count_brackets_prefix(s, i, bracket) + ((s[i] == bracket) as int),
{
}

proof fn lemma_prefix_imbalance(s: Seq<char>, k: int)
    requires
        valid_bracket_string(s),
        0 <= k <= s.len(),
        count_brackets_prefix(s, k, '<') < count_brackets_prefix(s, k, '>'),
    ensures !properly_nested(s),
{
}

/* helper modified by LLM (iteration 2): added explicit proof structure */
proof fn lemma_count_prefix_forall(s: Seq<char>, i: int)
    requires
        valid_bracket_string(s),
        0 <= i < s.len(),
        forall|k: int| 0 <= k <= i ==> count_brackets_prefix(s, k, '<') >= count_brackets_prefix(s, k, '>'),
        count_brackets_prefix(s, i + 1, '<') >= count_brackets_prefix(s, i + 1, '>'),
    ensures
        forall|k: int| 0 <= k <= i + 1 ==> count_brackets_prefix(s, k, '<') >= count_brackets_prefix(s, k, '>'),
{
    assert forall|k: int| 0 <= k <= i + 1 implies count_brackets_prefix(s, k, '<') >= count_brackets_prefix(s, k, '>') by {
        if k <= i {
            // In this case, the property is guaranteed by the forall in requires.
        } else {
            // In this case, k == i + 1, and the property is guaranteed by the second requires clause.
        }
    };
}
// </vc-helpers>

// <vc-spec>
fn correct_bracketing(brackets: Vec<char>) -> (result: bool)
    requires valid_bracket_string(brackets@)
    ensures result <==> properly_nested(brackets@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): no logical changes, original appears correct */
    let mut i: usize = 0;
    let mut balance: int = 0;
    while i < brackets.len()
        invariant
            0 <= i <= brackets.len(),
            valid_bracket_string(brackets@),
            balance == count_brackets_prefix(brackets@, i as int, '<') - count_brackets_prefix(brackets@, i as int, '>'),
            forall|k: int| 0 <= k <= (i as int) ==> 
                count_brackets_prefix(brackets@, k, '<') >= count_brackets_prefix(brackets@, k, '>'),
        decreases brackets.len() - i
    {
        lemma_count_prefix_increment(brackets@, i as int, '<');
        lemma_count_prefix_increment(brackets@, i as int, '>');

        let c = brackets[i];
        let next_balance = if c == '<' { balance + 1 } else { balance - 1 };

        if next_balance < 0 {
            lemma_prefix_imbalance(brackets@, (i + 1) as int);
            return false;
        }

        balance = next_balance;
        
        lemma_count_prefix_forall(brackets@, i as int);
        i = i + 1;
    }

    if balance == 0 {
        assert(properly_nested(brackets@));
        true
    } else {
        assert(!properly_nested(brackets@));
        false
    }
}
// </vc-code>


}

fn main() {}