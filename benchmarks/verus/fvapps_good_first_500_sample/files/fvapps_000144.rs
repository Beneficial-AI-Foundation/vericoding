// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn string_contains_char(s: Seq<char>, c: char) -> bool {
    exists|i: int| 0 <= i < s.len() && s[i] == c
}

spec fn is_alpha_char(c: char) -> bool;
// </vc-helpers>

// <vc-spec>
fn decode_string(s: &str) -> (result: String)
    ensures
        forall|c: char| string_contains_char(result@, c) ==> is_alpha_char(c),
        forall|c: char| string_contains_char(result@, c) ==>
            exists|c_orig: char| string_contains_char(s@, c_orig) && c == c_orig && is_alpha_char(c_orig)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>

}
fn main() {
    // println!("{}", decode_string("3[a]2[bc]"));
    // println!("{}", decode_string("3[a2[c]]"));
    // println!("{}", decode_string("2[abc]3[cd]ef"));
}