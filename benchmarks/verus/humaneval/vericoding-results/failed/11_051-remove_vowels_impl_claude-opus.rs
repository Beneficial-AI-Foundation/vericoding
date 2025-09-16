// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_vowel_spec(c: char) -> (result:bool) {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I'
        || c == 'O' || c == 'U'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed syntax error in lemma by using 'by' for proof block */
fn is_vowel(c: char) -> (result: bool)
    ensures
        result == is_vowel_spec(c),
{
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}

proof fn lemma_filter_step(s: Seq<char>, i: nat, c: char)
    requires
        i < s.len(),
        s[i as int] == c,
    ensures
        s.take((i + 1) as int).filter(|x: char| !is_vowel_spec(x)) ==
        if is_vowel_spec(c) {
            s.take(i as int).filter(|x: char| !is_vowel_spec(x))
        } else {
            s.take(i as int).filter(|x: char| !is_vowel_spec(x)).push(c)
        },
{
    let s_take_i = s.take(i as int);
    let s_take_i_plus_1 = s.take((i + 1) as int);
    assert(s_take_i_plus_1 == s_take_i.push(c));
    
    let filtered_i = s_take_i.filter(|x: char| !is_vowel_spec(x));
    let filtered_i_plus_1 = s_take_i_plus_1.filter(|x: char| !is_vowel_spec(x));
    
    assert forall|j: int| 0 <= j < filtered_i.len() implies filtered_i[j] == filtered_i_plus_1[j] by {
        assert(filtered_i[j] == filtered_i_plus_1[j]);
    }
    
    if is_vowel_spec(c) {
        assert(filtered_i_plus_1.len() == filtered_i.len());
        assert(filtered_i_plus_1 =~= filtered_i);
    } else {
        assert(filtered_i_plus_1.len() == filtered_i.len() + 1);
        assert(filtered_i_plus_1[filtered_i.len() as int] == c);
        assert(filtered_i_plus_1 =~= filtered_i.push(c));
    }
}
// </vc-helpers>

// <vc-spec>
fn remove_vowels(str: &[char]) -> (str_without_vowels: Vec<char>)

    ensures
        str_without_vowels@ == str@.filter(|x: char| !is_vowel_spec(x)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): No changes needed to code body */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < str.len()
        invariant
            0 <= i <= str.len(),
            result@ == str@.take(i as int).filter(|x: char| !is_vowel_spec(x)),
        decreases str.len() - i
    {
        let c = str[i];
        proof {
            lemma_filter_step(str@, i as nat, c);
        }
        if !is_vowel(c) {
            result.push(c);
        }
        i = i + 1;
    }
    assert(str@.take(str.len() as int) == str@);
    result
}
// </vc-code>

}
fn main() {}