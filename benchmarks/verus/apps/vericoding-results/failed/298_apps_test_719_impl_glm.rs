// <vc-preamble>
use vstd::prelude::*;

verus! {

#[verifier::external_body]
spec fn int_to_string(n: int) -> Seq<char> {
    unimplemented!()
}

spec fn valid_input(stdin_input: Seq<char>) -> bool {
    stdin_input.len() > 0 &&
    exists|k: int| k >= 1 && k <= 10000 && stdin_input == int_to_string(k).push('\n')
}

spec fn kth_perfect_number(k: int) -> int
    recommends k >= 1 && k <= 10000
{
    if k == 1 { 19 }
    else if k == 2 { 28 }
    else if k == 3 { 37 }
    else if k == 4 { 46 }
    else if k == 5 { 55 }
    else if k == 6 { 64 }
    else if k == 7 { 73 }
    else if k == 8 { 82 }
    else if k == 9 { 91 }
    else if k == 10 { 109 }
    else { 10 * (k - 9) + 99 }
}
// </vc-preamble>

// <vc-helpers>
fn compute_kth_perfect_number(k: u32) -> (result: u32)
    requires 1 <= k && k <= 10000
    ensures result as int == kth_perfect_number(k as int)
{
    if k == 1 { 19 }
    else if k == 2 { 28 }
    else if k == 3 { 37 }
    else if k == 4 { 46 }
    else if k == 5 { 55 }
    else if k == 6 { 64 }
    else if k == 7 { 73 }
    else if k == 8 { 82 }
    else if k == 9 { 91 }
    else if k == 10 { 109 }
    else { 10 * (k - 9) + 99 }
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: String) -> (result: String)
    requires valid_input(stdin_input@)
    ensures (exists|k: int| k >= 1 && k <= 10000 && 
        stdin_input@ == int_to_string(k).push('\n') &&
        result@ == int_to_string(kth_perfect_number(k)).push('\n')) &&
        result@.len() > 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): replaced trim_end_matches with manual newline removal */
    let mut chars: Vec<char> = stdin_input.chars().collect();
    chars.pop();
    let trimmed_str: String = chars.into_iter().collect();
    let k: u32 = trimmed_str.parse().unwrap();
    let perfect = compute_kth_perfect_number(k);
    let result = format!("{}\n", perfect);
    result
}
// </vc-code>


}

fn main() {}