// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed "len not supported" error by caching string length */
fn string_contains_char(s: &String, c: char) -> (b: bool)
    ensures b == s@.contains(c)
{
    let s_len = s.len();
    let mut i: usize = 0;
    while i < s_len
        invariant
            s_len == s@.len() as usize,
            i <= s_len,
            forall|j: int| 0 <= j < i as int ==> s@[j] != c,
        decreases s_len - i
    {
        if s.get_char(i) == c {
            assert(s@[i as int] == c);
            assert(s@.contains(c));
            return true;
        }
        i += 1;
    }
    assert(forall|j: int| 0 <= j < s@.len() ==> s@[j] != c);
    assert(!s@.contains(c));
    return false;
}

fn should_strip(c: char, chars: &Option<String>) -> (b: bool)
    ensures
        b == match chars {
            Some(s) => s@.contains(c),
            None => c.is_whitespace(),
        },
{
    match chars {
        Some(strip_chars) => string_contains_char(strip_chars, c),
        None => c.is_whitespace(),
    }
}

/* helper modified by LLM (iteration 5): fixed "len not supported" error by caching string length */
fn strip_one_string(s: &String, chars: &Option<String>) -> (result: String)
    ensures
        result@.len() <= s@.len(),
        exists|k: int| 0 <= k <= s@.len() as int && result@ == s@.subrange(k, s@.len() as int),
        (s@.len() == 0 ==> result@.len() == 0),
{
    let s_len = s.len();
    let mut i: usize = 0;
    while i < s_len
        invariant
            s_len == s@.len() as usize,
            i <= s_len,
            forall|j: int| 0 <= j < i as int ==> should_strip(s@[j], chars),
        decreases s_len - i
    {
        let c = s.get_char(i);
        if !should_strip(c, chars) {
            break;
        }
        i += 1;
    }
    s.substring_char(i, s_len).to_string()
}
// </vc-helpers>

// <vc-spec>
fn lstrip(a: Vec<String>, chars: Option<String>) -> (result: Vec<String>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() as int ==> {
            let original = #[trigger] a[i];
            let result_str = #[trigger] result[i];

            result_str@.len() <= original@.len() &&

            (exists|k: int| 0 <= k <= original@.len() as int && 
             result_str@ == original@.subrange(k, original@.len() as int)) &&

            (original@.len() == 0 ==> result_str@.len() == 0)
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): cached vector length to avoid potential "len not supported" errors */
{
    let mut result: Vec<String> = Vec::new();
    let a_len = a.len();
    let mut i: usize = 0;
    while i < a_len
        invariant
            a_len == a@.len() as usize,
            i <= a_len,
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> {
                let original = a[j];
                let result_str = result[j];

                result_str@.len() <= original@.len() &&

                (exists|k: int| 0 <= k <= original@.len() as int && 
                 result_str@ == original@.subrange(k, original@.len() as int)) &&

                (original@.len() == 0 ==> result_str@.len() == 0)
            },
        decreases a_len - i
    {
        let stripped_s = strip_one_string(&a[i], &chars);
        result.push(stripped_s);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}