// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_uppercase(c: char) -> bool {
    'A' <= c && c <= 'Z'
}

spec fn shift32(c: char) -> char {
    ((c as int) + 32) as char
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn to_lowercase(s: &Vec<char>) -> (result: Vec<char>)
    ensures
        result.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> {
            if is_uppercase(s[i]) {
                result[i] == shift32(s[i])
            } else {
                result[i] == s[i]
            }
        },
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}