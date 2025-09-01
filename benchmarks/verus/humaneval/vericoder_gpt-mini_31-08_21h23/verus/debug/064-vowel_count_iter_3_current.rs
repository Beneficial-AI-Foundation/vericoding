use vstd::prelude::*;

verus! {

spec fn is_vowel(c: char) -> (ret:bool) {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I'
        || c == 'O' || c == 'U'
}
// pure-end
// pure-end

spec fn vowels(s: Seq<char>) -> (ret:Seq<char>) {
    s.filter(|c| is_vowel(c))
}
// pure-end
// pure-end

spec fn inner_expr_vowels_count(s: &str, ret: u32) -> (ret:bool) {
    ret == vowels(s@).len() + if (s@.len() > 0 && (s@.last() == 'y' || s@.last() == 'Y')) {
        1int

    } else {
        0int
    }
}
// pure-end

// <vc-helpers>
proof fn vowels_single(c: char)
    ensures
        vowels(seq![c]) == if is_vowel(c) { seq![c] } else { seq![] }
{
    // This follows from the definition of filter on a single-element sequence.
    if is_vowel(c) {
        assert(vowels(seq![c]) == seq![c]);
    } else {
        assert(vowels(seq![c]) == seq![]);
    }
}

proof fn vowels_cons(first: char, t: Seq<char>)
    ensures
        vowels(seq![first] + t) == (if is_vowel(first) { seq![first] + vowels(t) } else { vowels(t) })
{
    // Direct case analysis on whether `first` is a vowel.
    if is_vowel(first) {
        assert(vowels(seq![first] + t) == seq![first] + vowels(t));
    } else {
        assert(vowels(seq![first] + t) == vowels(t));
    }
}

proof fn vowels_concat(s1: Seq<char>, s2: Seq<char>)
    ensures
        vowels(s1 + s2) == vowels(s1) + vowels(s2)
    decreases
        s1.len()
{
    if s1.len() == 0 {
        // s1 == seq![]
        assert(s1 + s2 == s2);
        assert(vowels(s1 + s2) == vowels(s2));
        assert(vowels(s1) == seq![]);
        assert(vowels(s1) + vowels(s2) == vowels(s2));
    } else {
        let first = s1@[0];
        let rest = s1[1..];
        assert(s1 == seq![first] + rest);
        // Use the cons lemma to expand vowels on seq![first] + (rest + s2)
        vowels_cons(first, rest + s2);
        // Use induction on the rest to split vowels(rest + s2)
        vowels_concat(rest, s2);
        // Now combine:
        // vowels(s1 + s2) == vowels(seq![first] + (rest + s2))
        assert(vowels(s1 + s2) == vowels(seq![first] + (rest + s2)));
        // from vowels_cons: vowels(seq![first] + (rest + s2)) == if is_vowel(first) { seq![first] + vowels(rest + s2) } else { vowels(rest + s2) }
        // from induction: vowels(rest + s2) == vowels(rest) + vowels(s2)
        if is_vowel(first) {
            assert(vowels(s1 + s2) == seq![first] + (vowels(rest) + vowels(s2)));
            assert(seq![first] + (vowels(rest) + vowels(s2)) == (seq![first] + vowels(rest)) + vowels(s2));
            assert((seq![first] + vowels(rest)) == (if is_vowel(first) { seq![first] + vowels(rest) } else { vowels(rest) })); // tautology
            assert(vowels(s1 + s2) == (if is_vowel(first) { seq![first] + vowels(rest) } else { vowels(rest) }) + vowels(s2));
        } else {
            assert(vowels(s1 + s2) == vowels(rest + s2));
            assert(vowels(rest + s2) == vowels(rest) + vowels(s2));
            assert(vowels(s1 + s2) == vowels(rest) + vowels(s2));
            assert(vowels(rest) == (if is_vowel(first) { seq![first] + vowels(rest) } else { vowels(rest) }) - seq![]); // harmless step
            assert(vowels(s1 + s2) == (if is_vowel(first) { seq![first] + vowels(rest) } else { vowels(rest) }) + vowels(s2));
        }
        // But (if is_vowel(first) { seq![first] + vowels(rest) } else { vowels(rest) }) == vowels(seq![first] + rest) == vowels(s1)
        assert(vowels(seq![first] + rest) == (if is_vowel(first) { seq![first] + vowels(rest) } else { vowels(rest) }));
        assert(vowels(s1 + s2) == vowels(s1) + vowels(s2));
    }
}

proof fn vowels_len_le(s: Seq<char>)
    ensures
        vowels(s).len() <= s.len()
    decreases
        s.len()
{
    if s.len() == 0 {
        assert(vowels
// </vc-helpers>

// <vc-spec>
fn vowels_count(s: &str) -> (ret: u32)
    // pre-conditions-start
    requires
        s@.len() <= u32::MAX,
    // pre-conditions-end
    // post-conditions-start
    ensures
        inner_expr_vowels_count(s, ret),
    // post-conditions-end
// </vc-spec>
// <vc-code>
proof fn vowels_single(c: char)
    ensures
        vowels(seq![c]) == if is_vowel(c) { seq![c] } else { seq![] }
{
    // This follows from the definition of filter on a single-element sequence.
    if is_vowel(c) {
        assert(vowels(seq![c]) == seq![c]);
    } else {
        assert(vowels(seq![c]) == seq![]);
    }
}

proof fn vowels_cons(first: char, t: Seq<char>)
    ensures
        vowels(seq![first] + t) == (if is_vowel(first) { seq![first] + vowels(t) } else { vowels(t) })
{
    // Direct case analysis on whether `first` is a vowel.
    if is_vowel(first) {
        assert(vowels(seq![first] + t) == seq![first] + vowels(t));
    } else {
        assert(vowels(seq![first] + t) == vowels(t));
    }
}

proof fn vowels_concat(s1: Seq<char>, s2: Seq<char>)
    ensures
        vowels(s1 + s2) == vowels(s1) + vowels(s2)
    decreases
        s1.len()
{
    if s1.len() == 0 {
        // s1 == seq![]
        assert(s1 + s2 == s2);
        assert(vowels(s1 + s2) == vowels(s2));
        assert(vowels(s1) == seq![]);
        assert(vowels(s1) + vowels(s2) == vowels(s2));
    } else {
        let first = s1@[0];
        let rest = s1[1..];
        assert(s1 == seq![first] + rest);
        // Use the cons lemma to expand vowels on seq![first] + (rest + s2)
        vowels_cons(first, rest + s2);
        // Use induction on the rest to split vowels(rest + s2)
        vowels_concat(rest, s2);
        // Now combine:
        // vowels(s1 + s2) == vowels(seq![first] + (rest + s2))
        assert(vowels(s1 + s2) == vowels(seq![first] + (rest + s2)));
        // from vowels_cons: vowels(seq![first] + (rest + s2)) == if is_vowel(first) { seq![first] + vowels(rest + s2) } else { vowels(rest + s2) }
        // from induction: vowels(rest + s2) == vowels(rest) + vowels(s2)
        if is_vowel(first) {
            assert(vowels(s1 + s2) == seq![first] + (vowels(rest) + vowels(s2)));
            assert(seq![first] + (vowels(rest) + vowels(s2)) == (seq![first] + vowels(rest)) + vowels(s2));
            assert((seq![first] + vowels(rest)) == (if is_vowel(first) { seq![first] + vowels(rest) } else { vowels(rest) })); // tautology
            assert(vowels(s1 + s2) == (if is_vowel(first) { seq![first] + vowels(rest) } else { vowels(rest) }) + vowels(s2));
        } else {
            assert(vowels(s1 + s2) == vowels(rest + s2));
            assert(vowels(rest + s2) == vowels(rest) + vowels(s2));
            assert(vowels(s1 + s2) == vowels(rest) + vowels(s2));
            assert(vowels(rest) == (if is_vowel(first) { seq![first] + vowels(rest) } else { vowels(rest) }) - seq![]); // harmless step
            assert(vowels(s1 + s2) == (if is_vowel(first) { seq![first] + vowels(rest) } else { vowels(rest) }) + vowels(s2));
        }
        // But (if is_vowel(first) { seq![first] + vowels(rest) } else { vowels(rest) }) == vowels(seq![first] + rest) == vowels(s1)
        assert(vowels(seq![first] + rest) == (if is_vowel(first) { seq![first] + vowels(rest) } else { vowels(rest) }));
        assert(vowels(s1 + s2) == vowels(s1) + vowels(s2));
    }
}

proof fn vowels_len_le(s: Seq<char>)
    ensures
        vowels(s).len() <= s.len()
    decreases
        s.len()
{
    if s.len() == 0 {
        assert(vowels
// </vc-code>

fn main() {}
}