// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_vowel_spec(c: char) -> (result:bool) {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I'
        || c == 'O' || c == 'U'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): provide vowel/consonant helpers matching spec */
spec fn is_consonant(c: char) -> bool { !is_vowel_spec(c) }

fn is_vowel(c: char) -> (result: bool)
    ensures
        result == is_vowel_spec(c),
{
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' ||
    c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}
// </vc-helpers>

// <vc-spec>
fn remove_vowels(str: &[char]) -> (str_without_vowels: Vec<char>)

    ensures
        str_without_vowels@ == str@.filter(|x: char| !is_vowel_spec(x)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): loop with sequence take/filter reasoning to meet postcondition */
    let mut res: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < str.len()
        invariant
            i <= str.len(),
            res@ == str@.take(i as int).filter(|x: char| !is_vowel_spec(x)),
        decreases str.len() - i
    {
        let c = str[i];
        proof { assert(c == str@[i as int]); }
        let b = is_vowel(c);
        proof { assert(b == is_vowel_spec(c)); }
        if !b {
            res.push(c);
            proof {
                assert(str@.take((i as int) + 1) == str@.take(i as int) + seq![str@[i as int]]);
                assert(str@.take((i as int) + 1).filter(|x: char| !is_vowel_spec(x))
                    == (str@.take(i as int) + seq![c]).filter(|x: char| !is_vowel_spec(x)));
                assert((str@.take(i as int) + seq![c]).filter(|x: char| !is_vowel_spec(x))
                    == str@.take(i as int).filter(|x: char| !is_vowel_spec(x))
                       + seq![c].filter(|x: char| !is_vowel_spec(x)));
                assert(seq![c].filter(|x: char| !is_vowel_spec(x)) == seq![c]);
            }
        } else {
            proof {
                assert(str@.take((i as int) + 1) == str@.take(i as int) + seq![str@[i as int]]);
                assert((str@.take(i as int) + seq![c]).filter(|x: char| !is_vowel_spec(x))
                    == str@.take(i as int).filter(|x: char| !is_vowel_spec(x))
                       + seq![c].filter(|x: char| !is_vowel_spec(x)));
                assert(seq![c].filter(|x: char| !is_vowel_spec(x)) == Seq::<char>::empty());
                assert((str@.take(i as int) + seq![c]).filter(|x: char| !is_vowel_spec(x))
                    == str@.take(i as int).filter(|x: char| !is_vowel_spec(x)));
            }
        }
        i = i + 1;
    }
    proof {
        assert(res@ == str@.take(str.len() as int).filter(|x: char| !is_vowel_spec(x)));
        assert(str@.take(str.len() as int) == str@);
    }
    res
}
// </vc-code>

}
fn main() {}