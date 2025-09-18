// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): used s@.len() instead of s.len() to fix compilation error */
fn is_alphanumeric_char_exec(c: char) -> (b: bool)
    ensures b == is_alphanumeric_char(c)
{
    ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') || ('0' <= c && c <= '9')
}

proof fn lemma_all_chars_alphanumeric_is_false(s: Seq<char>, i: int)
    requires
        0 <= i < s.len(),
        !is_alphanumeric_char(s[i]),
        all_chars_alphanumeric(s.subrange(0, i)),
    ensures !all_chars_alphanumeric(s),
    decreases s.len() - i,
{
    if i > 0 {
        lemma_all_chars_alphanumeric_is_false(s.skip(1), i - 1);
    }
}

fn string_isalnum_check(s: &String) -> (b: bool)
    ensures b == (s@.len() > 0 && all_chars_alphanumeric(s@)),
{
    if s@.len() == 0 {
        return false;
    }
    let mut i: usize = 0;
    while i < s@.len()
        invariant
            s@.len() > 0,
            0 <= i <= s@.len(),
            all_chars_alphanumeric(s@.subrange(0, i as int)),
    {
        let c = s.get_char(i);
        if !is_alphanumeric_char_exec(c) {
            proof {
                lemma_all_chars_alphanumeric_is_false(s@, i as int);
            }
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-helpers>

// <vc-spec>
spec fn is_alphanumeric_char(c: char) -> bool;

spec fn all_chars_alphanumeric(s: Seq<char>) -> bool
    decreases s.len()
{
    if s.len() == 0 {
        true
    } else {
        is_alphanumeric_char(s[0]) && all_chars_alphanumeric(s.skip(1))
    }
}

fn isalnum(a: Vec<String>) -> (result: Vec<bool>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> 
            result[i] == (a[i]@.len() > 0 && all_chars_alphanumeric(a[i]@))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): no changes needed, logic is sound and previous error was in helpers. */
{
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == (a[j]@.len() > 0 && all_chars_alphanumeric(a[j]@)),
    {
        let b = string_isalnum_check(&a[i]);
        result.push(b);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}