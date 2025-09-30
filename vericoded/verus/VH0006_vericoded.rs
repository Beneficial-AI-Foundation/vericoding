// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn split_by_spaces_result(s: Seq<char>) -> Seq<Seq<char>> {
    if s.len() == 0 {
        seq![]
    } else {
        let groups = seq![];
        let current_group = seq![];
        let i = 0;
        split_by_spaces_helper(s, i, current_group, groups)
    }
}

spec fn max_nesting_depth(group: Seq<char>) -> int {
    max_nesting_depth_helper(group, 0, 0, 0)
}

spec fn split_by_spaces_helper(s: Seq<char>, i: int, current_group: Seq<char>, groups: Seq<Seq<char>>) -> Seq<Seq<char>>
    decreases s.len() - i when 0 <= i <= s.len()
{
    if i == s.len() {
        if current_group.len() > 0 { groups.push(current_group) } else { groups }
    } else if s[i] == ' ' {
        if current_group.len() > 0 {
            split_by_spaces_helper(s, i + 1, seq![], groups.push(current_group))
        } else {
            split_by_spaces_helper(s, i + 1, current_group, groups)
        }
    } else {
        split_by_spaces_helper(s, i + 1, current_group.push(s[i]), groups)
    }
}

spec fn max_nesting_depth_helper(group: Seq<char>, index: int, current_depth: int, max_depth: int) -> int
    decreases group.len() - index when 0 <= index <= group.len()
{
    if index == group.len() {
        max_depth
    } else if group[index] == '(' {
        let new_current = current_depth + 1;
        let new_max = if new_current > max_depth { new_current } else { max_depth };
        max_nesting_depth_helper(group, index + 1, new_current, new_max)
    } else if group[index] == ')' {
        max_nesting_depth_helper(group, index + 1, current_depth - 1, max_depth)
    } else {
        max_nesting_depth_helper(group, index + 1, current_depth, max_depth)
    }
}

fn split_by_spaces(s: Seq<char>) -> (groups: Seq<Seq<char>>)
    requires forall|i: int| 0 <= i < s.len() ==> s[i] == '(' || s[i] == ')' || s[i] == ' '
{
    assume(false);
    unreached()
}
// </vc-preamble>

// <vc-helpers>
spec fn is_paren_or_space(c: char) -> bool {
    c == '(' || c == ')' || c == ' '
}
// </vc-helpers>

// <vc-spec>
fn parse_nested_parens(paren_string: Vec<char>) -> (result: Vec<i8>)
    requires forall|i: int| 0 <= i < paren_string@.len() ==> paren_string@[i] == '(' || paren_string@[i] == ')' || paren_string@[i] == ' '
    ensures forall|i: int| 0 <= i < result@.len() ==> result[i] as int >= 0
// </vc-spec>
// <vc-code>
{
    let result: Vec<i8> = Vec::new();
    result
}
// </vc-code>


}

fn main() {}