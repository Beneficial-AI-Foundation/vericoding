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
/* helper modified by LLM (iteration 3): make helper callable in proofs */
proof fn last_char_newline(s: Vec<char>)
    requires
        s.len() > 0,
        is_valid_input(s@),
    ensures
        s@[s.len() as int - 1] == '\n',
{
    // From the spec predicate we know the sequence view ends with '\n'
    assert((s@)[s.len() as int - 1] == '\n');
    // The Vec and its sequence view agree on indexing
    assert(s@[s.len() as int - 1] == (s@)[s.len() as int - 1]);
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
    /* code modified by LLM (iteration 3): return input and prove last char is newline */
    let result = s;
    proof {
        last_char_newline(result);
    }
    result
}

// </vc-code>


}

fn main() {}