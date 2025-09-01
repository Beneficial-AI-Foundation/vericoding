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

proof fn filter_append_one_char(s: Seq<char>, c: char, p: fn(char) -> bool)
    decreases s.len()
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
                // After push, res@ == previous + seq![ch]
                filter_append_one_char(str@[0..i-1], ch, not_is_vowel_spec);
                assert(res@ == (str@[0..i-1] + seq![ch]).filter(|x: char| !is_vowel_spec(x)));
                assert((str@[0..i-1] + seq![ch]) == str@[0..i]);
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