// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn is_alpha_char_exec(c: char) -> (b: bool)
    ensures
        b == is_alpha_char(c),
{
    ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z')
}

fn is_upper_char_exec(c: char) -> (b: bool)
    ensures
        b == is_upper_char(c),
{
    'A' <= c && c <= 'Z'
}

/* helper modified by LLM (iteration 4): fixed compilation errors with type casts and sequence indexing */
fn process_string(s: &String) -> (res: bool)
    ensures
        res == (s@.len() > 0 && has_alpha_chars(s@) && all_alpha_are_upper(s@)),
{
    let s_seq = s@;
    if s_seq.is_empty() {
        return false;
    }

    let mut has_alpha = false;
    let mut all_upper = true;
    let mut i: int = 0 as int;
    while i < s_seq.len() as int
        invariant
            0 <= i <= s_seq.len() as int,
            has_alpha == has_alpha_chars(s_seq.subrange(0, i)),
            all_upper == all_alpha_are_upper(s_seq.subrange(0, i)),
        decreases s_seq.len() as int - i
    {
        let c = s_seq@[i];
        if is_alpha_char_exec(c) {
            has_alpha = true;
            if !is_upper_char_exec(c) {
                all_upper = false;
            }
        }
        i = i + 1 as int;
    }
    has_alpha && all_upper
}
// </vc-helpers>

// <vc-spec>
spec fn is_alpha_char(c: char) -> bool;

spec fn is_upper_char(c: char) -> bool;

spec fn has_alpha_chars(s: Seq<char>) -> bool {
    exists|i: int| 0 <= i < s.len() && is_alpha_char(s[i])
}

spec fn all_alpha_are_upper(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() && is_alpha_char(s[i]) ==> is_upper_char(s[i])
}

fn isupper(a: Vec<String>) -> (result: Vec<bool>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] result[i] == {
            let s = a[i]@;
            s.len() > 0 && has_alpha_chars(s) && all_alpha_are_upper(s)
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): fixed type mismatches and spec indexing in loop invariant */
{
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> #[trigger] result@[j] == {
                let s = a@[j]@;
                s.len() > 0 && has_alpha_chars(s) && all_alpha_are_upper(s)
            },
    {
        let s: &String = &a[i];
        let b = process_string(s);
        result.push(b);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}