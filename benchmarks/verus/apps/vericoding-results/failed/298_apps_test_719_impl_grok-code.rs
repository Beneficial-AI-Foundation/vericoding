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
/* helper modified by LLM (iteration 5): fixed type error by using usize instead of nat, and added ensures that input matches int_to_string(result).push('\n') */
fn parse_k(input: Seq<char>) -> (result: usize)
    requires
        input.len() > 0,
        input@[input.len() as int - 1] == '\n',
        input.len() <= 6,  // to bound, since k<=10000
    ensures
        result >= 1,
        result <= 10000,
        input == int_to_string(result as int).push('\n'),
{
    let cleaned_len: usize = input.len() as usize - 1;
    let cleaned = input.subrange(0, cleaned_len as int);
    let mut num: usize = 0;
    let mut i: usize = 0;
    while i < cleaned_len
        invariant
            i <= cleaned_len,
    {
        let digit: u8 = cleaned@[i as int] as u8 - '0' as u8;
        num = num * 10 + digit as usize;
        i = i + 1;
    }
    num
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
/* code modified by LLM (iteration 5): implement main logic to parse k, compute perf_num, and return string */
{
    let k: usize = parse_k(stdin_input@);
    let perf_num: usize;
    if k == 1 {
        perf_num = 19;
    } else if k == 2 {
        perf_num = 28;
    } else if k == 3 {
        perf_num = 37;
    } else if k == 4 {
        perf_num = 46;
    } else if k == 5 {
        perf_num = 55;
    } else if k == 6 {
        perf_num = 64;
    } else if k == 7 {
        perf_num = 73;
    } else if k == 8 {
        perf_num = 82;
    } else if k == 9 {
        perf_num = 91;
    } else if k == 10 {
        perf_num = 109;
    } else {
        perf_num = 10 * (k - 9) + 99;
    }
    let result = perf_num.to_string() + "\n";
    result
}
// </vc-code>


}

fn main() {}