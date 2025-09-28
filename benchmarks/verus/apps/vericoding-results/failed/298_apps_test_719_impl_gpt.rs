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
/* helper modified by LLM (iteration 5): choose witness k from valid_input proof */
proof fn witness_k(si: Seq<char>) -> (res: int)
    requires
        valid_input(si),
    ensures
        1 <= res && res <= 10000,
        si == int_to_string(res).push('\n'),
{
    let k: int = choose|kk: int| kk >= 1 && kk <= 10000 && si == int_to_string(kk).push('\n');
    proof {
        assert(k >= 1 && k <= 10000 && si == int_to_string(k).push('\n'));
    }
    k
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
    /* code modified by LLM (iteration 5): construct result using vstd::string::String::from_seq */
    let k: int = witness_k(stdin_input@);
    let seq_out: Seq<char> = int_to_string(kth_perfect_number(k)).push('\n');
    proof { assert(seq_out.len() > 0); }
    let result = vstd::string::String::from_seq(seq_out);
    result
}
// </vc-code>


}

fn main() {}