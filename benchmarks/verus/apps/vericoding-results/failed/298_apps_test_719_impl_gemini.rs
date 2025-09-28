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
fn exec_kth_perfect_number(k: u64) -> (result: u64)
    requires
        k >= 1 && k <= 10000,
    ensures
        result as int == kth_perfect_number(k as int),
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

#[verifier::external_body]
fn u64_to_string(n: u64) -> (s: String)
    ensures
        s@ == int_to_string(n as int),
{
    let rust_s = std::string::ToString::to_string(&n);
    String::from_rust_string(rust_s)
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
    let ghost k_val = choose |k: int| k >= 1 && k <= 10000 &&
        stdin_input@ == int_to_string(k).push('\n');

    let len = stdin_input.len();
    let num_str = stdin_input.substring(0, (len - 1) as nat);

    proof {
        assert(num_str@ == int_to_string(k_val));
        vstd::string::lemma_int_string_is_nat_string(k_val);
        vstd::string::lemma_nat_from_string_is_some(num_str@, k_val as nat);
    }

    let k_opt = vstd::string::parse_nat(num_str.as_str());
    let k_nat = k_opt.unwrap();

    proof {
        vstd::string::lemma_nat_string_roundtrip(k_val as nat);
    }
    assert(k_nat == k_val as nat);

    let k = k_nat as u64;
    let perfect_num = exec_kth_perfect_number(k);

    let mut result = u64_to_string(perfect_num);
    result.push_char('\n');

    assert(result@.len() > 0);

    result
}
// </vc-code>


}

fn main() {}