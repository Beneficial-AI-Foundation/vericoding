// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_vowel_spec(c: char) -> (result:bool) {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I'
        || c == 'O' || c == 'U'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [use correct std lib lemmas for proof] */
proof fn lemma_subrange_succ<T>(s: Seq<T>, i: int)
    requires 0 <= i < s.len(),
    ensures s.subrange(0, i + 1) == s.subrange(0, i) + seq![s[i]],
{
    vstd::seq_lib::lemma_subrange_join(s, 0, i, i + 1);
    vstd::seq_lib::lemma_subrange_one(s, i);
}

fn is_vowel(c: char) -> (result: bool)
    ensures result == is_vowel_spec(c),
{
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I'
        || c == 'O' || c == 'U'
}
// </vc-helpers>

// <vc-spec>
fn remove_vowels(str: &[char]) -> (str_without_vowels: Vec<char>)

    ensures
        str_without_vowels@ == str@.filter(|x: char| !is_vowel_spec(x)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): [provide detailed lemmas for loop invariant proof] */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < str.len()
        invariant
            i <= str.len(),
            result@ == str@.subrange(0, i as int).filter(|x: char| !is_vowel_spec(x)),
        decreases str.len() - i
    {
        let c = str[i];
        if !is_vowel(c) {
            result.push(c);
        }

        proof {
            let i_int = i as int;
            let c_spec = str@[i_int];
            let filter_fn = |x: char| !is_vowel_spec(x);

            lemma_subrange_succ(str@, i_int);
            vstd::seq_lib::lemma_filter_add(str@.subrange(0, i_int), seq![c_spec], filter_fn);
            vstd::seq_lib::lemma_filter_of_one(c_spec, filter_fn);
        }

        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}