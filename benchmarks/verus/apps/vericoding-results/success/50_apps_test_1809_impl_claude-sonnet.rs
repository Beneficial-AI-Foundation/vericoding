// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_valid_input(s: Seq<char>) -> bool {
    s.len() >= 5 && s[s.len() as int - 1] == '\n'
}

spec fn calculate_result_from_input(s: Seq<char>) -> Seq<char> {
    s /* placeholder implementation */
}
// </vc-preamble>

// <vc-helpers>
// Helper functions for processing input
spec fn remove_trailing_newline(s: Seq<char>) -> Seq<char> {
    if s.len() > 0 && s[s.len() as int - 1] == '\n' {
        s.subrange(0, s.len() as int - 1)
    } else {
        s
    }
}

spec fn add_trailing_newline(s: Seq<char>) -> Seq<char> {
    s.push('\n')
}

/* helper modified by LLM (iteration 3): Fixed lemma syntax by adding proof block */
proof fn lemma_newline_preservation(s: Seq<char>)
    requires s.len() > 0, s[s.len() as int - 1] == '\n'
    ensures add_trailing_newline(remove_trailing_newline(s)) == s
{
}

/* helper modified by LLM (iteration 3): Fixed lemma syntax by adding proof block */
proof fn lemma_result_has_newline(s: Seq<char>)
    requires s.len() > 0
    ensures 
        add_trailing_newline(s).len() > 0,
        add_trailing_newline(s)[add_trailing_newline(s).len() as int - 1] == '\n'
{
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    requires 
        s.len() > 0,
        (exists|i: int| 0 <= i < s.len() as int && s@[i] == '\n'),
        is_valid_input(s@),
    ensures 
        result.len() > 0,
        result@[result.len() as int - 1] == '\n'
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Added decreases clause to fix compilation error */
    let mut result = Vec::new();
    
    // Copy all characters from input
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == s@[j],
        decreases s.len() - i
    {
        result.push(s[i]);
        i += 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}