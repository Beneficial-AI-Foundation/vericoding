// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_valid_input(input: &str) -> bool {
    let lines = split_lines(input);
    lines.len() >= 3 && 
    parse_int(lines[0]) > 0 &&
    parse_int_array(lines[1]).len() == parse_int(lines[0]) &&
    parse_int_array(lines[2]).len() == parse_int(lines[0])
}

spec fn get_initial_sum(input: &str) -> int
    recommends is_valid_input(input)
{
    let lines = split_lines(input);
    sum_seq(parse_int_array(lines[1]))
}

spec fn get_target_sum(input: &str) -> int
    recommends is_valid_input(input)
{
    let lines = split_lines(input);
    sum_seq(parse_int_array(lines[2]))
}

spec fn sum_seq(nums: Seq<int>) -> int
    decreases nums.len()
{
    if nums.len() == 0 {
        0
    } else {
        nums[0] + sum_seq(nums.subrange(1, nums.len() as int))
    }
}

uninterp spec fn split_lines(input: &str) -> Seq<&str>;
uninterp spec fn parse_int(s: &str) -> int;
uninterp spec fn parse_int_array(s: &str) -> Seq<int>;
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(input: &str) -> (result: String)
    requires is_valid_input(input)
    ensures (result == "Yes") <==> get_initial_sum(input) >= get_target_sum(input)
// </vc-spec>
// <vc-code>
{
    assume(false);
    "No".to_string()
}
// </vc-code>


}

fn main() {}