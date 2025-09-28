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
/* helper modified by LLM (iteration 5): fixing compilation by naming return type result, adjusting exec logic to properly return false for unbalanced parens */
fn is_balanced_exec(parens: &Vec<char>) -> (result: bool)
    requires valid_paren_string(parens@)
    ensures result <==> is_balanced(parens@)
{
    let mut depth = 0;
    for i in 0..parens.len()
        invariant
            0 <= i <= parens.len(),
            0 <= depth,
            is_balanced_helper(parens@.subrange(0, i), 0) >= 0 || is_balanced_helper(parens@.subrange(0, i), 0) == -1
    {
        if parens[i] == '(' {
            depth += 1;
        } else {
            if depth > 0 {
                depth -= 1;
            } else {
                return false;
            }
        }
    }
    depth == 0
}
// </vc-helpers>

// <vc-spec>
fn match_parens(lst: Vec<Vec<char>>) -> (result: Vec<char>)
    requires valid_input(seq![lst[0]@, lst[1]@])
    ensures correct_output(seq![lst[0]@, lst[1]@], result@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): keeping the main logic implementation with calls to exec helper */
{
    let mut combined1 = lst[0].clone();
    combined1.append(&mut lst[1].clone());
    let res1 = is_balanced_exec(&combined1);
    let mut combined2 = lst[1].clone();
    combined2.append(&mut lst[0].clone());
    let res2 = is_balanced_exec(&combined2);
    if res1 || res2 {
        vec!['Y', 'e', 's']
    } else {
        vec!['N', 'o']
    }
}
// </vc-code>


}

fn main() {}