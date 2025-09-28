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
/* helper modified by LLM (iteration 3): changed from int to i32 for executable code */
fn exec_is_balanced_helper(s: &Vec<char>, initial_depth: i32) -> (result: i32)
    ensures result == is_balanced_helper(s@, initial_depth as int)
{
    let mut depth: i32 = initial_depth;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            depth == is_balanced_helper(s@.subrange(0, i as int), initial_depth as int),
            (depth as int) >= 0
        decreases s.len() - i
    {
        let c = s[i];
        if c == '(' {
            depth = depth + 1;
        } else if c == ')' {
            depth = depth - 1;
        }
        if depth < 0 {
            return -1;
        }
        i += 1;
    }
    depth
}

fn check_concat(s1: &Vec<char>, s2: &Vec<char>) -> (result: bool)
    ensures result == is_balanced(s1@ + s2@)
{
    let d1 = exec_is_balanced_helper(s1, 0);
    if d1 < 0 {
        return false;
    }
    let d2 = exec_is_balanced_helper(s2, d1);
    d2 == 0
}
// </vc-helpers>

// <vc-spec>
fn match_parens(lst: Vec<Vec<char>>) -> (result: Vec<char>)
    requires valid_input(seq![lst[0]@, lst[1]@])
    ensures correct_output(seq![lst[0]@, lst[1]@], result@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): updated to use fixed helper functions with i32 */
{
    if check_concat(&lst[0], &lst[1]) || check_concat(&lst[1], &lst[0]) {
        vec!['Y','e','s']
    } else {
        vec!['N','o']
    }
}
// </vc-code>


}

fn main() {}