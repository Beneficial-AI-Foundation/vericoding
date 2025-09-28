// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

proof fn lemma_all_chars_alpha_empty()
    ensures
        all_chars_alpha(Seq::empty()) == true,
{
}

proof fn lemma_all_chars_alpha_cons(c: char, s: Seq<char>)
    requires
        is_alpha_char(c),
        all_chars_alpha(s),
    ensures
        all_chars_alpha(Seq::new(1, |i: int| c).add(s)) == true,
{
}

proof fn lemma_all_chars_alpha_non_alpha_first(c: char, s: Seq<char>)
    requires
        !is_alpha_char(c),
    ensures
        all_chars_alpha(Seq::new(1, |i: int| c).add(s)) == false,
{
}

/* helper modified by LLM (iteration 5): Replace String.is_empty() with manual length check */
fn is_alpha_char_runtime(c: char) -> (result: bool)
    ensures
        result == is_alpha_char(c),
{
    let c_u8 = c as u8;
    (c_u8 >= 97u8 && c_u8 <= 122u8) || (c_u8 >= 65u8 && c_u8 <= 90u8)
}

fn check_string_alpha(s: &String) -> (result: bool)
    ensures
        result == (s@.len() > 0 && all_chars_alpha(s@)),
{
    if s.len() == 0 {
        false
    } else {
        let mut chars = s.chars();
        let mut i: usize = 0;
        let mut all_alpha = true;
        while i < s.len()
            invariant
                0 <= i <= s.len(),
                all_alpha == (i > 0 ==> all_chars_alpha(s@.subrange(0, i as int))),
            decreases s.len() - i,
        {
            let c = chars.next().unwrap();
            if !is_alpha_char_runtime(c) {
                all_alpha = false;
                break;
            }
            i = i + 1;
        }
        all_alpha
    }
}

// </vc-helpers>

// <vc-spec>
spec fn is_alpha_char(c: char) -> bool {
    ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z')
}

spec fn all_chars_alpha(s: Seq<char>) -> bool 
    decreases s.len()
{
    if s.len() == 0 {
        true
    } else {
        is_alpha_char(s[0]) && all_chars_alpha(s.skip(1))
    }
}

fn isalpha(a: Vec<String>) -> (result: Vec<bool>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> 
            result[i as int] == (a[i as int]@.len() > 0 && all_chars_alpha(a[i as int]@)),
        forall|i: int| 0 <= i < a.len() ==> 
            (a[i as int]@.len() == 0 ==> result[i as int] == false),
        forall|i: int| 0 <= i < a.len() ==> 
            (a[i as int]@.len() > 0 ==> (result[i as int] <==> all_chars_alpha(a[i as int]@))),
        forall|i: int| 0 <= i < a.len() ==> 
            (result[i as int] == true ==> a[i as int]@.len() > 0),
        forall|i: int| 0 <= i < a.len() ==> 
            (result[i as int] == true ==> all_chars_alpha(a[i as int]@))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Keep implementation with fixed string length check */
    let mut result_vec = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result_vec.len() == i,
            forall|j: int| 0 <= j < i ==> result_vec[j as int] == (a[j as int]@.len() > 0 && all_chars_alpha(a[j as int]@)),
            forall|j: int| 0 <= j < i ==> (a[j as int]@.len() == 0 ==> result_vec[j as int] == false),
            forall|j: int| 0 <= j < i ==> (a[j as int]@.len() > 0 ==> (result_vec[j as int] <==> all_chars_alpha(a[j as int]@))),
            forall|j: int| 0 <= j < i ==> (result_vec[j as int] == true ==> a[j as int]@.len() > 0),
            forall|j: int| 0 <= j < i ==> (result_vec[j as int] == true ==> all_chars_alpha(a[j as int]@)),
        decreases a.len() - i,
    {
        let is_alpha = check_string_alpha(&a[i]);
        result_vec.push(is_alpha);
        i = i + 1;
    }
    result_vec
}
// </vc-code>


}
fn main() {}