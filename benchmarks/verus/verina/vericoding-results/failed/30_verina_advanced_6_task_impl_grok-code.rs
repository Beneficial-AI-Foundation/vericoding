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
/* helper modified by LLM (iteration 5): Fixed casting from int to u32 to allow executable code usage */
fn to_lower_exec(c: char) -> char {
    if 'A' <= c && c <= 'Z' {
        ((c as u32 + 32) as char)
    } else {
        c
    }
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
/* code modified by LLM (iteration 5): Maintained while loop with invariants to verify all vowels present after normalization */
{
    let s_view = s@;
    let mut a_found = false;
    let mut e_found = false;
    let mut i_found = false;
    let mut o_found = false;
    let mut u_found = false;
    let mut index = 0;
    while index < s_view.len()
        invariant
            index <= s_view.len(),
            a_found == exists|j: int| 0 <= j < index && to_lower(s@[j]) == 'a',
            e_found == exists|j: int| 0 <= j < index && to_lower(s@[j]) == 'e',
            i_found == exists|j: int| 0 <= j < index && to_lower(s@[j]) == 'i',
            o_found == exists|j: int| 0 <= j < index && to_lower(s@[j]) == 'o',
            u_found == exists|j: int| 0 <= j < index && to_lower(s@[j]) == 'u',
    {
        let c = s_view[index];
        if to_lower_exec(c) == 'a' {
            a_found = true;
        } else if to_lower_exec(c) == 'e' {
            e_found = true;
        } else if to_lower_exec(c) == 'i' {
            i_found = true;
        } else if to_lower_exec(c) == 'o' {
            o_found = true;
        } else if to_lower_exec(c) == 'u' {
            u_found = true;
        }
        index += 1;
    }
    a_found && e_found && i_found && o_found && u_found
}
// </vc-code>

}
fn main() {}