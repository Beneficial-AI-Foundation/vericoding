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
proof fn lemma_balanced_helper_add(s1: Seq<char>, s2: Seq<char>, depth: int) -> (result: int)
    requires valid_paren_string(s1) && valid_paren_string(s2)
    ensures result == is_balanced_helper(s1.add(s2), depth) && result == is_balanced_helper(s2, is_balanced_helper(s1, depth))
    decreases s1.len()
{
    if s1.len() == 0 {
        is_balanced_helper(s2, depth)
    } else {
        let c = s1[0];
        let rest = s1.subrange(1, s1.len() as int);
        if c == '(' {
            lemma_balanced_helper_add(rest, s2, depth + 1)
        } else if c == ')' {
            if depth > 0 {
                lemma_balanced_helper_add(rest, s2, depth - 1)
            } else {
                -1
            }
        } else {
            lemma_balanced_helper_add(rest, s2, depth)
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn match_parens(lst: Vec<Vec<char>>) -> (result: Vec<char>)
    requires valid_input(seq![lst[0]@, lst[1]@])
    ensures correct_output(seq![lst[0]@, lst[1]@], result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed int usage in exec mode */
    let s1 = lst[0].clone();
    let s2 = lst[1].clone();
    
    ghost {
        let balance_s1 = is_balanced_helper(s1@, 0);
        let balance_s2 = is_balanced_helper(s2@, 0);
        let concat1_balance = lemma_balanced_helper_add(s1@, s2@, 0);
        let concat2_balance = lemma_balanced_helper_add(s2@, s1@, 0);
        let balanced_s1_then_s2 = is_balanced_helper(s2@, balance_s1) == 0;
        let balanced_s2_then_s1 = is_balanced_helper(s1@, balance_s2) == 0;
        
        let result_chars = if balanced_s1_then_s2 || balanced_s2_then_s1 {
            seq!['Y', 'e', 's']
        } else {
            seq!['N', 'o']
        };
    }
    
    let balanced_s1_then_s2_exec = is_balanced_helper_exec(s1@, s2@);
    let balanced_s2_then_s1_exec = is_balanced_helper_exec(s2@, s1@);
    
    let result_chars = if balanced_s1_then_s2_exec || balanced_s2_then_s1_exec {
        vec!['Y', 'e', 's']
    } else {
        vec!['N', 'o']
    };
    
    result_chars
}
// </vc-code>


}

fn main() {}