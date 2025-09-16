// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Added invariant `len <= s.len()` to prove index safety. */
fn get_prefix(s: &Vec<u8>, len: usize) -> (prefix: Vec<u8>)
    requires
        len <= s.len(),
    ensures
        prefix@ == s@.subrange(0, len as int),
{
    let mut prefix = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i <= len,
            len <= s.len(),
            prefix.len() == i,
            forall|j: int| 0 <= j < i ==> prefix@[j] == s@[j],
        decreases len - i
    {
        prefix.push(s[i]);
        i = i + 1;
    }
    prefix
}
// </vc-helpers>

// <vc-spec>
fn all_prefixes(s: &Vec<u8>) -> (prefixes: Vec<Vec<u8>>)

    ensures
        prefixes.len() == s.len(),
        forall|i: int| #![auto] 0 <= i < s.len() ==> prefixes[i]@ == s@.subrange(0, i + 1),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Confirmed logic is correct and made no changes. */
    let mut prefixes: Vec<Vec<u8>> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            prefixes.len() == i,
            forall|j: int| #![auto] 0 <= j < i ==> prefixes[j]@ == s@.subrange(0, j + 1),
        decreases s.len() - i
    {
        let current_prefix = get_prefix(s, i + 1);
        prefixes.push(current_prefix);
        i = i + 1;
    }
    prefixes
}
// </vc-code>

}
fn main() {}