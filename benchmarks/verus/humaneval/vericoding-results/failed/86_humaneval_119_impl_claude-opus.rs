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
/* helper modified by LLM (iteration 5): Changed from int to i32 for executable code */
fn is_balanced_helper_exec(s: &Vec<char>, start: usize, end: usize, depth: i32) -> (result: i32)
    requires
        start <= end <= s.len(),
        valid_paren_string(s@.subrange(start as int, end as int)),
    ensures
        result as int == is_balanced_helper(s@.subrange(start as int, end as int), depth as int),
    decreases end - start
{
    if start == end {
        depth
    } else {
        let c = s[start];
        if c == '(' {
            is_balanced_helper_exec(s, start + 1, end, depth + 1)
        } else if c == ')' {
            if depth > 0 {
                is_balanced_helper_exec(s, start + 1, end, depth - 1)
            } else {
                -1
            }
        } else {
            is_balanced_helper_exec(s, start + 1, end, depth)
        }
    }
}

fn concat_vecs(v1: &Vec<char>, v2: &Vec<char>) -> (result: Vec<char>)
    ensures result@ == v1@.add(v2@)
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < v1.len()
        invariant
            0 <= i <= v1.len(),
            result@ == v1@.subrange(0, i as int),
    {
        result.push(v1[i]);
        i = i + 1;
    }
    let mut j = 0;
    while j < v2.len()
        invariant
            0 <= j <= v2.len(),
            result@ == v1@.add(v2@.subrange(0, j as int)),
    {
        result.push(v2[j]);
        j = j + 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn match_parens(lst: Vec<Vec<char>>) -> (result: Vec<char>)
    requires valid_input(seq![lst[0]@, lst[1]@])
    ensures correct_output(seq![lst[0]@, lst[1]@], result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Changed to use i32 instead of int for executable code */
    let concat1 = concat_vecs(&lst[0], &lst[1]);
    let result1 = is_balanced_helper_exec(&concat1, 0, concat1.len(), 0);
    
    if result1 == 0 {
        return vec!['Y', 'e', 's'];
    }
    
    let concat2 = concat_vecs(&lst[1], &lst[0]);
    let result2 = is_balanced_helper_exec(&concat2, 0, concat2.len(), 0);
    
    if result2 == 0 {
        vec!['Y', 'e', 's']
    } else {
        vec!['N', 'o']
    }
}
// </vc-code>


}

fn main() {}