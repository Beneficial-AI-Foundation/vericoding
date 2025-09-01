use vstd::prelude::*;

verus! {

spec fn is_vowel_spec(c: char) -> (result:bool) {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I'
        || c == 'O' || c == 'U'
}
// pure-end

// <vc-helpers>
spec fn not_is_vowel_spec(c: char) -> bool {
    !is_vowel_spec(c)
}

proof fn filter_append_one_char(s: Seq<char>, c: char)
    decreases s.len()
    ensures (s.filter(|x: char| not_is_vowel_spec(x)) + if not_is_vowel_spec(c) { seq![c] } else { seq![] }) == (s + seq![c]).filter(|x: char| not_is_vowel_spec(x))
{
    if s.len() == 0 {
        assert(s == seq![]);
        assert(s.filter(|x: char| not_is_vowel_spec(x)) == seq![]);
        assert((s + seq![c]).filter(|x: char| not_is_vowel_spec(x)) == if not_is_vowel_spec(c) { seq![c] } else { seq![] });
    } else {
        let h: char = s[0];
        let tail: Seq<char> = s[1..];
        filter_append_one_char(tail, c);
        if not_is_vowel_spec(h) {
            assert(s.filter(|x: char| not_is_vowel_spec(x)) == seq![h] + tail.filter(|x: char| not_is_vowel_spec(x)));
            assert((s + seq![c]).filter(|x: char| not_is_vowel_spec(x)) == seq![h] + (tail + seq![c]).filter(|x: char| not_is_vowel_spec(x)));
            assert(tail.filter(|x: char| not_is_vowel_spec(x)) + if not_is_vowel_spec(c) { seq![c] } else { seq![] } == (tail + seq![c]).filter(|x: char| not_is_vowel_spec(x)));
            assert(seq![h] + tail.filter(|x: char| not_is_vowel_spec(x)) + if not_is_vowel_spec(c) { seq![c] } else { seq![] } == seq![h] + (tail + seq![c]).filter(|x: char| not_is_vowel_spec(x)));
            assert((s.filter(|x: char| not_is_vowel_spec(x)) + if not_is_vowel_spec(c) { seq![c] } else { seq![] }) == (s + seq![c]).filter(|x: char| not_is_vowel_spec(x)));
        } else {
            assert(s.filter(|x: char| not_is_vowel_spec(x)) == tail.filter(|x: char| not_is_vowel_spec(x)));
            assert((s + seq![c]).filter(|x: char| not_is_vowel_spec(x)) == (tail + seq![c]).filter(|x: char| not_is_vowel_spec(x)));
            assert(tail.filter(|x: char| not_is_vowel_spec(x)) + if not_is_vowel_spec(c) { seq![c] } else { seq![] } == (tail + seq![c]).filter(|x: char| not_is_vowel_spec(x)));
            assert((s.filter(|x: char| not_is_vowel_spec(x)) + if not_is_vowel_spec(c) { seq![c] } else { seq![] }) == (s + seq![c]).filter(|x: char| not_is_vowel_spec(x)));
        }
    }
}

fn build_prefix(str: &[char], i: usize) -> Vec<char>
    requires i <= str.len()
    decreases i
    ensures result@ == str@[0..i].filter(|x: char| !is_vowel_spec(x))
{
    if i == 0 {
        Vec::new()
    } else {
        let mut res = build_prefix(str, i - 1);
        let ch: char = str[i - 1];
        if !is_vowel_spec(ch) {
            res.push(ch);
            proof {
                // res before push satisfies res@ == str@[0..i-1].filter(...)
                // After push, by lemma filter_append_one_char we have:
                filter_append_one_char(str@[0..i-1], ch);
                assert(res@ == (str@[0..i-1].filter(|x: char| not_is_vowel_spec(x)) + seq![ch]));
                assert((str@[0..i-1] + seq![ch]).filter(|x: char| not_is_vowel_spec(x)) == (str@[0..i-1]).filter(|x: char| not_is_vowel_spec(x)) + seq![ch]);
                assert((str@[0..i-1] + seq![ch]) == str@[0..i]);
                assert(res@ == str@[0..i].filter(|x: char| not_is_vowel_spec(x)));
            }
        }
        res
    }
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
    // impl-start
    build_prefix(str, str.len())
    // impl-end
}
// </vc-code>

} // verus!
fn main() {}