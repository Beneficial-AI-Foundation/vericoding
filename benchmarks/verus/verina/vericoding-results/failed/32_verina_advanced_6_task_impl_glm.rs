// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn to_lower(c: char) -> char {
    if 'A' <= c && c <= 'Z' {
        ((c as int + 32) as char)
    } else {
        c
    }
}

spec fn normalize_str(s: &str) -> Seq<char> {
    s.view().map_values(|c| to_lower(c))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed invariant syntax by removing braces */
fn vec_contains(vec: &Vec<char>, c: char) -> (result: bool)
    ensures result == vec.view().contains(c)
{
    let mut found = false;
    let mut i = 0;
    while i < vec.len()
        invariant 0 <= i <= vec.len(),
        invariant !found ==> forall |j: int| 0<=j<i ==> vec@[j] != c,
    {
        if vec@[i] == c {
            found = true;
        }
        i += 1;
    }
    found
}

fn normalize_str_exec(s: &str) -> (result: Vec<char>)
    ensures result.view() == normalize_str(s)
{
    let mut vec = Vec::new();
    let chars_seq: Seq<char> = s.view();
    let mut i = 0;
    while i < chars_seq.len()
        invariant 0 <= i <= chars_seq.len(),
        invariant vec.view() == chars_seq.subrange(0, i).map_values(|c: char| to_lower(c)),
    {
        let c = chars_seq[i];
        let lower = if 'A' <= c && c <= 'Z' {
            ((c as u8 + 32) as char)
        } else {
            c
        };
        vec.push(lower);
        i += 1;
    }
    vec
}
// </vc-helpers>

// <vc-spec>
fn all_vowels(s: &str) -> (result: bool)
    ensures
        result <==> (
            normalize_str(s).contains('a') &&
            normalize_str(s).contains('e') &&
            normalize_str(s).contains('i') &&
            normalize_str(s).contains('o') &&
            normalize_str(s).contains('u')
        ),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): no changes needed */
{
    let normalized = normalize_str_exec(s);
    vec_contains(&normalized, 'a') &&
    vec_contains(&normalized, 'e') &&
    vec_contains(&normalized, 'i') &&
    vec_contains(&normalized, 'o') &&
    vec_contains(&normalized, 'u')
}
// </vc-code>

}
fn main() {}