// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: Seq<char>) -> bool {
    true
}

spec fn valid_assignment(input: Seq<char>, assignment: Seq<nat>) -> bool {
    true
}

spec fn has_all_three_groups(assignment: Seq<nat>) -> bool {
    (exists|i: int| 0 <= i < assignment.len() && assignment[i] == 1) &&
    (exists|i: int| 0 <= i < assignment.len() && assignment[i] == 2) &&
    (exists|i: int| 0 <= i < assignment.len() && assignment[i] == 3)
}

spec fn calculate_assignment_cost(input: Seq<char>, assignment: Seq<nat>) -> nat {
    composition_cost(assignment) + adjustment_cost(input, assignment)
}

spec fn composition_cost(assignment: Seq<nat>) -> nat {
    let group_a_size = count_group_members(assignment, 1);
    let group_b_size = count_group_members(assignment, 2);
    let group_c_size = count_group_members(assignment, 3);
    (if group_a_size > 0 { ((group_a_size - 1) * 10) as nat } else { 0nat }) +
    (if group_b_size > 0 { ((group_b_size - 1) * 10) as nat } else { 0nat }) +
    (if group_c_size > 0 { ((group_c_size - 1) * 10) as nat } else { 0nat })
}

spec fn adjustment_cost(input: Seq<char>, assignment: Seq<nat>) -> nat {
    let lines = split_lines(input);
    let (n, a, b, c) = parse_first_line_bamboo(lines[0]);
    let sum_a = calculate_group_sum(input, assignment, 1);
    let sum_b = calculate_group_sum(input, assignment, 2);
    let sum_c = calculate_group_sum(input, assignment, 3);
    abs_diff(sum_a, a) + abs_diff(sum_b, b) + abs_diff(sum_c, c)
}

spec fn count_group_members(assignment: Seq<nat>, group: nat) -> nat
    decreases assignment.len()
{
    if assignment.len() == 0 {
        0nat
    } else {
        (if assignment[0] == group { 1nat } else { 0nat }) + count_group_members(assignment.drop_first(), group)
    }
}

spec fn calculate_group_sum(input: Seq<char>, assignment: Seq<nat>, group: nat) -> nat {
    0nat
}

spec fn abs_diff(a: nat, b: nat) -> nat {
    if a >= b { (a - b) as nat } else { (b - a) as nat }
}

spec fn split_lines(s: Seq<char>) -> Seq<Seq<char>> {
    Seq::<Seq<char>>::empty()
}

spec fn parse_first_line_bamboo(line: Seq<char>) -> (nat, nat, nat, nat) {
    (0nat, 0nat, 0nat, 0nat)
}

spec fn parse_bamboo_length(line: Seq<char>) -> nat {
    0nat
}

fn int_to_string(n: nat) -> String {
    "".to_string()
}

spec fn string_to_int(s: Seq<char>) -> nat {
    0nat
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Vec<u8>) -> (result: Vec<u8>)
// </vc-spec>
// <vc-code>
{
    assume(false);
    Vec::new()
}
// </vc-code>


}

fn main() {}