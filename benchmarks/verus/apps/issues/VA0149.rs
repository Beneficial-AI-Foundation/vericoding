// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn split_lines(input: &str) -> Seq<&str>
    uninterp;

spec fn parse_integer(s: &str) -> int
    uninterp;

spec fn count_sizes(sizes: Seq<&str>) -> Map<&str, nat>
    uninterp;

spec fn count_unmatched_sizes(prev_sizes: Map<&str, nat>, current_sizes: Seq<&str>) -> nat
    uninterp;

spec fn int_to_string(n: nat) -> String
    uninterp;

spec fn valid_input(stdin_input: &str) -> bool {
    let lines = split_lines(stdin_input);
    lines.len() >= 1 && {
        let n = parse_integer(lines[0]);
        n >= 0 && lines.len() >= (2 * n + 1) && 
        (forall|i: int| 1 <= i <= 2 * n ==> 
            i < lines.len() && lines[i].len() > 0)
    }
}

spec fn compute_mismatches(stdin_input: &str) -> nat
    decreases stdin_input.len()
{
    let lines = split_lines(stdin_input);
    let n = parse_integer(lines[0]);
    if n == 0 { 
        0 
    } else {
        let prev_sizes = count_sizes(lines.subrange(1, n + 1));
        let current_sizes = lines.subrange(n + 1, 2 * n + 1);
        count_unmatched_sizes(prev_sizes, current_sizes)
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: &str) -> (result: String)
    requires 
        stdin_input.len() > 0,
        valid_input(stdin_input),
    ensures 
        result.len() > 0,
        result.as_bytes()[result.len()-1] == b'\n' || 
            (result.len() > 1 && result.as_bytes().subrange(result.len()-2, result.len()) == seq![b'\r', b'\n']),
        exists|mismatches: nat| 
            result == int_to_string(mismatches) + "\n" && 
            mismatches == compute_mismatches(stdin_input),
        ({
            let lines = split_lines(stdin_input);
            let n = parse_integer(lines[0]);
            n >= 0 ==> {
                let mismatches = compute_mismatches(stdin_input);
                mismatches <= n &&
                result == int_to_string(mismatches) + "\n"
            }
        }),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    String::new()
    // impl-end
}
// </vc-code>


}

fn main() {}