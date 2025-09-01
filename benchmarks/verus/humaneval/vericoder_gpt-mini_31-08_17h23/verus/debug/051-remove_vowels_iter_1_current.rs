use vstd::prelude::*;

verus! {

spec fn is_vowel_spec(c: char) -> (result:bool) {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I'
        || c == 'O' || c == 'U'
}
// pure-end

// <vc-helpers>
// <vc-helpers>
spec fn not_is_vowel_spec(c: char) -> bool {
    !is_vowel_spec(c)
}

proof fn filter_append_one_char(s: Seq<char>, c: char, p: fn(char) -> bool)
    ensures (s.filter(|x: char| p(x)) + if p(c) { seq![c] } else { seq![] }) == (s + seq![c]).filter(|x: char| p(x))
{
    if s.len() == 0 {
        // s == []
        assert(s == seq![]);
        assert(s.filter(|x: char| p(x)) == seq![]);
        assert((s + seq![c]).filter(|x: char| p(x)) == if p(c) { seq![c] } else { seq![] });
    } else {
        let h: char = s[0];
        let tail: Seq<char> = s[1..];
        // induction on tail
        filter_append_one_char(tail, c, p);
        if p(h) {
            // s.filter = seq![h] + tail.filter
            assert(s.filter(|x: char| p(x)) == seq![h] + tail.filter(|x: char| p(x)));
            // (s + [c]).filter = seq![h] + (tail + [c]).filter
            assert((s + seq![c]).filter(|x: char| p(x)) == seq![h] + (tail + seq![c]).filter(|x: char| p(x)));
            // by induction (tail.filter + if p(c) {[c]} else {[]}) == (tail + [c]).filter
            assert(tail.filter(|x: char| p(x)) + if p(c) { seq![c] } else { seq![] } == (tail + seq![c]).filter(|x: char| p(x)));
            // combine
            assert(seq![h] + tail.filter(|x: char| p(x)) + if p(c) { seq![c] } else { seq![] } == seq![h] + (tail + seq![c]).filter(|x: char| p(x)));
            // if p(h) then seq![h] + tail.filter + cond == seq![h] + (tail + [c]).filter == (s + [c]).filter
            assert((s.filter(|x: char| p(x)) + if p(c) { seq![c] } else { seq![] }) == (s + seq![c]).filter(|x: char| p(x)));
        } else {
            // s.filter = tail.filter
            assert(s.filter(|x: char| p(x)) == tail.filter(|x: char| p(x)));
            // (s + [c]).filter = (tail + [c]).filter
            assert((s + seq![c]).filter(|x: char| p(x)) == (tail + seq![c]).filter(|x: char| p(x)));
            // by induction tail.filter + cond == (tail + [c]).filter
            assert(tail.filter(|x: char| p(x)) + if p(c) { seq![c] } else { seq![] } == (tail + seq![c]).filter(|x: char| p(x)));
            // combine
            assert((s.filter(|x: char| p(x)) + if p(c) { seq![c] } else { seq![] }) == (s + seq![c]).filter(|x: char| p(x)));
        }
    }
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn remove_vowels(str: &[char]) -> (str_without_vowels: Vec<char>)
    // post-conditions-start
    ensures
        str_without_vowels@ == str@.filter(|x: char| !is_vowel_spec(x)),
    // post-conditions-end
// </vc-spec>
// <vc-code>
// <vc-code>
{
    // impl-start
    let mut res: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < str.len() {
        invariant i <= str.len();
        invariant res@ == str@[0..i].filter(|x: char| !is_vowel_spec(x));
        {
            let ch: char = str[i];
            if !is_vowel_spec(ch) {
                // Before pushing, res@ == str@[0..i].filter(...)
                // After push, res@ == old_res@ + [ch], and by lemma this equals str@[0..i+1].filter(...)
                res.push(ch);
                proof {
                    // Use lemma for the prefix str@[0..i] and element ch with predicate not_is_vowel_spec
                    filter_append_one_char(str@[0..i], ch, not_is_vowel_spec);
                    // After push, res@ == previous + seq![ch] by Vec::push specification
                    // The verifier knows the effect of push; assert to help proof search
                    assert(res@ == str@[0..i].filter(|x: char| !is_vowel_spec(x)) + seq![ch]);
                    assert(res@ == (str@[0..i] + seq![ch]).filter(|x: char| !is_vowel_spec(x)));
                    // str@[0..i+1] == str@[0..i] + seq![ch]
                    assert((str@[0..i] + seq![ch]) == str@[0..i+1]);
                    assert(res@ == str@[0..i+1].filter(|x: char| !is_vowel_spec(x)));
                }
            } else {
                proof {
                    // No push; res@ remains equal to str@[0..i].filter(...)
                    // Show it equals str@[0..i+1].filter(...) when current char is a vowel
                    // Use lemma to rewrite (str@[0..i].filter + if p(ch) {[ch]} else {[]}) == (str@[0..i] + [ch]).filter
                    filter_append_one_char(str@[0..i], ch, not_is_vowel_spec);
                    // Since not_is_vowel_spec(ch) is false, the lemma gives str@[0..i].filter + [] == (str@[0..i]+[ch]).filter
                    assert(str@[0..i].filter(|x: char| !is_vowel_spec(x)) == (str@[0..i] + seq![ch]).filter(|x: char| !is_vowel_spec(x)));
                    assert((str@[0..i] + seq![ch]) == str@[0..i+1]);
                    assert(res@ == str@[0..i+1].filter(|x: char| !is_vowel_spec(x)));
                }
            }
            i = i + 1;
        }
    }
    res
    // impl-end
}
// </vc-code>
// </vc-code>

} // verus!
fn main() {}