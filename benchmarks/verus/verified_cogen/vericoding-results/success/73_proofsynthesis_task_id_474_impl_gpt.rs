// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn inner_epxr_replace_chars(str1: &Vec<char>, old_char: char, new_char: char, i: int) -> (result: char) {
    if str1[i] == old_char {
        new_char
    } else {
        str1[i]
    }
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_inner_char(v: &Vec<char>, old_char: char, new_char: char, i: int)
    requires 0 <= i < v.len()
    ensures inner_epxr_replace_chars(v, old_char, new_char, i) == (if v[i] == old_char { new_char } else { v[i] })
{ }
// </vc-helpers>

// <vc-spec>
fn replace_chars(str1: &Vec<char>, old_char: char, new_char: char) -> (result: Vec<char>)

    ensures
        str1@.len() == result@.len(),
        forall|i: int|
            0 <= i < str1.len() ==> result[i] == inner_epxr_replace_chars(str1, old_char, new_char, i),
// </vc-spec>
// <vc-code>
{
    let n = str1.len();
    let mut out: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            out@.len() == i as int,
            i as int <= n as int,
            forall|j: int| 0 <= j < i as int ==> out@[j] == inner_epxr_replace_chars(str1, old_char, new_char, j),
            n == str1.len(),
        decreases (n - i) as int
    {
        let ch = if str1[i] == old_char { new_char } else { str1[i] };
        out.push(ch);
        i = i + 1;
    }
    out
}
// </vc-code>

}
fn main() {}