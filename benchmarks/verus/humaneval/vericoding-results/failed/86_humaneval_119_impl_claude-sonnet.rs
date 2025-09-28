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
/* helper modified by LLM (iteration 5): Fixed depth tracking and overflow issues */
fn check_balanced(s: &Vec<char>) -> (result: bool)
    ensures result == is_balanced(s@)
{
    let mut depth: isize = 0;
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            depth >= 0,
            depth == is_balanced_helper(s@.subrange(0, i as int), 0),
        decreases s.len() - i
    {
        if s[i] == '(' {
            depth = depth + 1;
        } else if s[i] == ')' {
            if depth == 0 {
                return false;
            }
            depth = depth - 1;
        }
        i += 1;
    }
    depth == 0
}

fn combine_and_check(first: &Vec<char>, second: &Vec<char>) -> (result: bool)
    requires
        valid_paren_string(first@),
        valid_paren_string(second@),
    ensures result == is_balanced(first@.add(second@))
{
    let mut combined = Vec::new();
    let mut i = 0;
    while i < first.len()
        invariant
            0 <= i <= first.len(),
            combined@ == first@.subrange(0, i as int),
        decreases first.len() - i
    {
        combined.push(first[i]);
        i += 1;
    }
    i = 0;
    while i < second.len()
        invariant
            0 <= i <= second.len(),
            combined@ == first@.add(second@.subrange(0, i as int)),
        decreases second.len() - i
    {
        combined.push(second[i]);
        i += 1;
    }
    check_balanced(&combined)
}
// </vc-helpers>

// <vc-spec>
fn match_parens(lst: Vec<Vec<char>>) -> (result: Vec<char>)
    requires valid_input(seq![lst[0]@, lst[1]@])
    ensures correct_output(seq![lst[0]@, lst[1]@], result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added bounds checks for vector access */
    if lst.len() < 2 {
        return vec!['N', 'o'];
    }
    
    let first_second = combine_and_check(&lst[0], &lst[1]);
    let second_first = combine_and_check(&lst[1], &lst[0]);
    
    if first_second || second_first {
        vec!['Y', 'e', 's']
    } else {
        vec!['N', 'o']
    }
}
// </vc-code>


}

fn main() {}