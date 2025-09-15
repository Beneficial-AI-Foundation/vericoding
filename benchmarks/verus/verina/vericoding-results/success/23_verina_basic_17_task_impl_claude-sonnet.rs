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
/* helper modified by LLM (iteration 4): added exec mode version of is_uppercase */
fn is_uppercase_exec(c: char) -> (result: bool)
    ensures result == is_uppercase(c)
{
    'A' <= c && c <= 'Z'
}

/* helper modified by LLM (iteration 4): added exec mode version of shift32 */
fn shift32_exec(c: char) -> (result: char)
    requires is_uppercase(c)
    ensures result == shift32(c)
{
    ((c as u8) + 32) as char
}
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
    /* code modified by LLM (iteration 4): use with_capacity to preserve length property */
    let mut result = Vec::with_capacity(s.len());
    let mut i = 0;
    while i < s.len()
        invariant
            result.len() == i,
            i <= s.len(),
            forall|j: int| 0 <= j < i ==> {
                if is_uppercase(s[j]) {
                    result[j] == shift32(s[j])
                } else {
                    result[j] == s[j]
                }
            },
        decreases s.len() - i
    {
        let c = s[i];
        if is_uppercase_exec(c) {
            result.push(shift32_exec(c));
        } else {
            result.push(c);
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}