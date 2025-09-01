use vstd::prelude::*;

verus! {

spec fn is_vowel_spec(c: char) -> (result:bool) {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I'
        || c == 'O' || c == 'U'
}
// pure-end

// <vc-helpers>
spec fn is_not_vowel(c: char) -> bool {
    !is_vowel_spec(c)
}

proof fn filter_lemma(s: Seq<char>, i: int)
    requires
        0 <= i <= s.len() as int,
    ensures
        s.filter(|x: char| is_not_vowel(x)) == s.subrange(0, i).filter(|x: char| is_not_vowel(x)).add(s.subrange(i, s.len() as int).filter(|x: char| is_not_vowel(x))),
    decreases s.len() as int - i,
{
    if i < s.len() as int {
        filter_lemma(s, i + 1);
    }
}

proof fn filter_empty_lemma(s: Seq<char>)
    ensures
        s.filter(|x: char| is_not_vowel(x)) == Seq::empty(),
{
    if s.len() > 0 {
        filter_lemma(s, 0);
    }
}

proof fn filter_cons_lemma(s: Seq<char>, c: char)
    ensures
        s.push(c).filter(|x: char| is_not_vowel(x)) == 
            if is_not_vowel(c) {
                s.filter(|x: char| is_not_vowel(x)).push(c)
            } else {
                s.filter(|x: char| is_not_vowel(x))
            },
{
    filter_lemma(s.push(c), s.len() as int);
}
// </vc-helpers>

// <vc-spec>
fn remove_vowels(str: &[char]) -> (str_without_vowels: Vec<char>)
    // post-conditions-start
    ensures
        str_without_vowels@ == str@.filter(|x: char| !is_vowel_spec(x)),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut str_without_vowels = Vec::new();
    let mut i: usize = 0;
    while i < str.len()
        invariant
            i <= str.len(),
            str_without_vowels@ == str@.subrange(0, i as int).filter(|x: char| !is_vowel_spec(x)),
    {
        let c = str[i];
        if !is_vowel_spec(c) {
            str_without_vowels.push(c);
            proof {
                filter_cons_lemma(str@.subrange(0, i as int).filter(|x: char| !is_vowel_spec(x)), c);
            }
        } else {
            proof {
                filter_cons_lemma(str@.subrange(0, i as int).filter(|x: char| !is_vowel_spec(x)), c);
            }
        }
        i += 1;
    }
    proof {
        filter_lemma(str@, str.len() as int);
    }
    str_without_vowels
}
// </vc-code>

} // verus!
fn main() {}