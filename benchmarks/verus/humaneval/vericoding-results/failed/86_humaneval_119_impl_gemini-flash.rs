// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_paren_string(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] == '(' || s[i] == ')'
}

spec fn is_balanced_helper(s: Seq<char>, depth: int) -> int
    decreases s.len()
{
    if s.len() == 0 {
        depth
    } else if s[0] == '(' {
        is_balanced_helper(s.subrange(1, s.len() as int), depth + 1)
    } else if s[0] == ')' {
        if depth > 0 {
            is_balanced_helper(s.subrange(1, s.len() as int), depth - 1)
        } else {
            -1
        }
    } else {
        is_balanced_helper(s.subrange(1, s.len() as int), depth)
    }
}

spec fn is_balanced(s: Seq<char>) -> bool {
    is_balanced_helper(s, 0) == 0
}

spec fn valid_input(lst: Seq<Seq<char>>) -> bool {
    lst.len() == 2 && valid_paren_string(lst[0]) && valid_paren_string(lst[1])
}

spec fn yes_string() -> Seq<char> {
    seq!['Y', 'e', 's']
}

spec fn no_string() -> Seq<char> {
    seq!['N', 'o']
}

spec fn correct_output(lst: Seq<Seq<char>>, result: Seq<char>) -> bool {
    (result == yes_string() || result == no_string()) &&
    (result == yes_string() <==> (is_balanced(lst[0].add(lst[1])) || is_balanced(lst[1].add(lst[0]))))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed unused helper and changed is_balanced_vec_spec to use Seq<char> */
spec fn is_balanced_vec_spec(s_combined: Seq<char>) -> bool {
    is_balanced_helper(s_combined, 0) == 0
}
// </vc-helpers>

// <vc-spec>
fn match_parens(lst: Vec<Vec<char>>) -> (result: Vec<char>)
    requires valid_input(seq![lst[0]@, lst[1]@])
    ensures correct_output(seq![lst[0]@, lst[1]@], result@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): corrected method call to use `add` directly on sequences */
{
    let s0_vec = &lst[0];
    let s1_vec = &lst[1];

    let combined1_seq = s0_vec@.add(s1_vec@);
    let combined2_seq = s1_vec@.add(s0_vec@);

    let balanced1 = is_balanced_vec_spec(combined1_seq);
    let balanced2 = is_balanced_vec_spec(combined2_seq);

    if balanced1 || balanced2 {
        vstd::vec::Vec::from_seq(yes_string())
    } else {
        vstd::vec::Vec::from_seq(no_string())
    }
}
// </vc-code>


}

fn main() {}