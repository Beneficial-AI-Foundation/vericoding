// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(s: Seq<u8>) -> bool {
    s.len() >= 4 && forall|i: int| 0 <= i < 4 ==> b'0' <= s[i] <= b'9'
}

spec fn char_pair_to_int(c1: u8, c2: u8) -> int 
    recommends b'0' <= c1 <= b'9' && b'0' <= c2 <= b'9'
{
    (c1 as int - b'0' as int) * 10 + (c2 as int - b'0' as int)
}

spec fn valid_month(n: int) -> bool {
    1 <= n <= 12
}

spec fn get_first_pair(s: Seq<u8>) -> int 
    recommends valid_input(s)
{
    char_pair_to_int(s[0], s[1])
}

spec fn get_second_pair(s: Seq<u8>) -> int 
    recommends valid_input(s)
{
    char_pair_to_int(s[2], s[3])
}

spec fn correct_result(s: Seq<u8>, result: Seq<u8>) -> bool 
    recommends valid_input(s)
{
    let s1 = get_first_pair(s);
    let s2 = get_second_pair(s);
    let s1_valid = valid_month(s1);
    let s2_valid = valid_month(s2);
    (s1_valid && s2_valid ==> result == "AMBIGUOUS\n".as_bytes()) &&
    (s1_valid && !s2_valid ==> result == "MMYY\n".as_bytes()) &&
    (!s1_valid && s2_valid ==> result == "YYMM\n".as_bytes()) &&
    (!s1_valid && !s2_valid ==> result == "NA\n".as_bytes())
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: Vec<u8>) -> (result: Vec<u8>)
    requires valid_input(stdin_input@),
    ensures (result@ == "AMBIGUOUS\n".as_bytes() || 
             result@ == "MMYY\n".as_bytes() || 
             result@ == "YYMM\n".as_bytes() || 
             result@ == "NA\n".as_bytes()) &&
            correct_result(stdin_input@, result@)
// </vc-spec>
// <vc-code>
{
    assume(false);
    Vec::new()
}
// </vc-code>


}

fn main() {}