// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_vowel_spec(c: char) -> (result:bool) {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I'
        || c == 'O' || c == 'U'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): convert usize to int for seq operations */
spec fn usize_to_int(i: usize) -> int { i as int }
// </vc-helpers>

// <vc-spec>
fn remove_vowels(str: &[char]) -> (str_without_vowels: Vec<char>)

    ensures
        str_without_vowels@ == str@.filter(|x: char| !is_vowel_spec(x)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate and push non-vowel chars; maintain invariant using Seq.slice */
    let mut out: Vec<char> = Vec::new();
    let n = str.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            out@ == (str@).slice(0, usize_to_int(i)).filter(|x: char| !is_vowel_spec(x)),
        decreases n - i
    {
        let c = str[i];
        if !is_vowel_spec(c) {
            out.push(c);
        }
        i = i + 1;
    }
    out
}
// </vc-code>

}
fn main() {}