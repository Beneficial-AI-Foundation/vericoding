// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Avoided unsupported is_empty() by using chars().next() and skip() to check emptiness and iterate, ensuring spec compliance without direct empty checks. */
fn is_string_alpha_exec(input: &String) -> (b: bool)
    ensures
        b == string_is_alpha(input@)
{
    if let Some(first) = input.chars().next() {
        if !((('A' <= first && first <= 'Z') || ('a' <= first && first <= 'z'))) {
            return false;
        }
        for c in input.chars().skip(1) {
            if !((('A' <= c && c <= 'Z') || ('a' <= c && c <= 'z'))) {
                return false;
            }
        }
        true
    } else {
        false
    }
}
// </vc-helpers>

// <vc-spec>
spec fn is_alpha_char(c: char) -> bool {
    ('A' <= c && c <= 'Z') || ('a' <= c && c <= 'z')
}

spec fn string_is_alpha(s: Seq<char>) -> bool {
    s.len() > 0 && forall|i: int| 0 <= i < s.len() ==> is_alpha_char(s[i])
}

fn is_alpha(input: Vec<String>) -> (ret: Vec<bool>)
    ensures
        ret.len() == input.len(),
        forall|i: int| 0 <= i < input.len() ==> 
            ret[i] == string_is_alpha(input[i]@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): No changes needed as the implementation is correct and calls the updated helper. */
{
    let mut ret: Vec<bool> = Vec::with_capacity(input.len());
    let mut i = 0;
    while i < input.len()
        invariant
            ret.len() == i,
            forall|k: int| 0 <= k < i ==> ret[k] == string_is_alpha(input[k]@)
        decreases input.len() - i
    {
        if is_string_alpha_exec(&input[i]) {
            ret.push(true);
        } else {
            ret.push(false);
        }
        i += 1;
    }
    ret
}
// </vc-code>


}
fn main() {}