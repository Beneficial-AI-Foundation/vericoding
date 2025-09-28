// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn clean_input(s: Seq<char>) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 { 
        s
    } else if s[s.len() - 1] == '\n' || s[s.len() - 1] == '\r' || s[s.len() - 1] == ' ' { 
        clean_input(s.subrange(0, s.len() - 1))
    } else { 
        s
    }
}

spec fn contains_digit_nine(s: Seq<char>) -> bool {
    exists|i: int| 0 <= i < s.len() && s[i] == '9'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): predicate to identify characters trimmed by clean_input */
spec fn is_trim_char(c: char) -> bool { c == '\n' || c == '\r' || c == ' ' }

/* helper modified by LLM (iteration 5): compute the trimmed length equivalent to clean_input */
spec fn trim_len(s: Seq<char>) -> nat
    decreases s.len()
{
    if s.len() == 0 { 0 } else if is_trim_char(s[s.len() - 1]) { trim_len(s.subrange(0, s.len() - 1)) } else { s.len() }
}

/* helper modified by LLM (iteration 5): clean_input length equals trim_len */
proof fn lemma_clean_input_len_eq(s: Seq<char>)
    ensures clean_input(s).len() == trim_len(s)
    decreases s.len()
{
    if s.len() == 0 {
    } else if is_trim_char(s[s.len() - 1]) {
        lemma_clean_input_len_eq(s.subrange(0, s.len() - 1));
    } else {
        assert(trim_len(s) == s.len());
        assert(clean_input(s).len() == s.len());
    }
}

/* helper modified by LLM (iteration 5): clean_input preserves the non-trimmed prefix */
proof fn lemma_clean_input_preserves_prefix(s: Seq<char>)
    ensures
        forall|i:int| 0 <= i < trim_len(s) ==> clean_input(s)[i] == s[i],
    decreases s.len()
{
    if s.len() == 0 {
    } else if is_trim_char(s[s.len() - 1]) {
        lemma_clean_input_preserves_prefix(s.subrange(0, s.len() - 1));
    } else {
        assert(trim_len(s) == s.len());
        assert(clean_input(s) == s);
    }
}

/* helper modified by LLM (iteration 5): equivalence of contains_digit_nine after trimming */
proof fn lemma_contains_nine_clean_equiv(s: Seq<char>)
    ensures
        contains_digit_nine(clean_input(s)) == exists|i:int| 0 <= i < trim_len(s) && s[i] == '9',
{
    lemma_clean_input_len_eq(s);
    lemma_clean_input_preserves_prefix(s);

    assert(contains_digit_nine(clean_input(s)) ==> exists|i:int| 0 <= i < trim_len(s) && s[i] == '9') by {
        if contains_digit_nine(clean_input(s)) {
            let i = choose|i:int| 0 <= i < clean_input(s).len() && clean_input(s)[i] == '9';
            assert(0 <= i && i < trim_len(s));
            assert(s[i] == '9') by {
                assert(clean_input(s)[i] == s[i]);
            }
        }
    }

    assert((exists|i:int| 0 <= i < trim_len(s) && s[i] == '9') ==> contains_digit_nine(clean_input(s))) by {
        if exists|i:int| 0 <= i < trim_len(s) && s[i] == '9' {
            let i = choose|i:int| 0 <= i < trim_len(s) && s[i] == '9';
            assert(i < clean_input(s).len());
            assert(clean_input(s)[i] == '9') by {
                assert(clean_input(s)[i] == s[i]);
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: &str) -> (result: String)
    requires stdin_input@.len() > 0
    ensures 
        result@ == seq!['Y', 'e', 's', '\n'] || result@ == seq!['N', 'o', '\n'],
        result@ == seq!['Y', 'e', 's', '\n'] <==> contains_digit_nine(clean_input(stdin_input@)),
        result@ == seq!['N', 'o', '\n'] <==> !contains_digit_nine(clean_input(stdin_input@))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): replace unsupported iterator any with manual next() loop */
    let mut it = stdin_input.chars();
    let mut has_nine = false;
    loop {
        match it.next() {
            Some(c) => {
                if c == '9' {
                    has_nine = true;
                    break;
                }
            }
            None => break,
        }
    }
    let result = if has_nine { "Yes\n" } else { "No\n" }.to_string();
    proof {
        lemma_contains_nine_clean_equiv(stdin_input@);
    }
    result
}
// </vc-code>


}

fn main() {}