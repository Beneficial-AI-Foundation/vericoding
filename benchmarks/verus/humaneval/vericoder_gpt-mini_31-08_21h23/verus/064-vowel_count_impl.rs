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
        assert(s1 + s2 == s2);
        assert(vowels(s1 + s2) == vowels(s2));
        assert(vowels(s1) == seq![]);
        assert(vowels(s1) + vowels(s2) == vowels(s2));
    } else {
        let first = s1@[0];
        let rest = s1[1..];
        assert(s1 == seq![first] + rest);
        vowels_cons(first, rest + s2);
        vowels_concat(rest, s2);
        assert(vowels(s1 + s2) == vowels(seq![first] + (rest + s2)));
        if is_vowel(first) {
            assert(vowels(s1 + s2) == seq![first] + (vowels(rest) + vowels(s2)));
            assert(seq![first] + (vowels(rest) + vowels(s2)) == (seq![first] + vowels(rest)) + vowels(s2));
            assert((seq![first] + vowels(rest)) == (if is_vowel(first) { seq![first] + vowels(rest) } else { vowels(rest) }));
            assert(vowels(s1 + s2) == (if is_vowel(first) { seq![first] + vowels(rest) } else { vowels(rest) }) + vowels(s2));
        } else {
            assert(vowels(s1 + s2) == vowels(rest + s2));
            assert(vowels(rest + s2) == vowels(rest) + vowels(s2));
            assert(vowels(s1 + s2) == vowels(rest) + vowels(s2));
            assert(vowels(rest) == (if is_vowel(first) { seq![first] + vowels(rest) } else { vowels(rest) }) - seq![]);
            assert(vowels(s1 + s2) == (if is_vowel(first) { seq![first] + vowels(rest) } else { vowels(rest) }) + vowels(s2));
        }
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
        assert(vowels(s) == seq![]);
        assert(vowels(s).len() == 0);
        assert(vowels(s).len() <= s.len());
    } else {
        let first = s@[0];
        let rest = s[1..];
        assert(s == seq![first] + rest);
        vowels_cons(first, rest);
        vowels_len_le(rest);
        if is_vowel(first) {
            // vowels(s) == seq![first] + vowels(rest)
            assert(vowels(s).len() == 1 + vowels(rest).len());
            assert(vowels(rest).len() <= rest.len());
            assert(1 + vowels(rest).len() <= 1 + rest.len());
            assert(1 + rest.len() == s.len());
            assert(vowels(s).len() <= s.len());
        } else {
            // vowels(s) == vowels(rest)
            assert(vowels(s).len() == vowels(rest).len());
            assert(vowels(rest).len() <= rest.len());
            assert(rest.len() < s.len());
            assert(vowels(s).len() <= s.len());
        }
    }
}
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
{
    let sl = s@;
    let mut i: nat = 0;
    let mut count: nat = 0;
    // initial invariant holds: count == vowels(sl[0..0]).len()
    assert(count == vowels(sl[0..i]).len());
    while i < sl.len()
        invariant i <= sl.len();
        invariant count == vowels(sl[0..i]).len();
        decreases sl.len() - i
    {
        if is_vowel(sl@[i]) {
            let prev = count;
            count = prev + 1;
            proof {
                // prev == vowels(sl[0..i]).len()
                assert(prev == vowels(sl[0..i]).len());
                // vowels(sl[0..i+1]) == vowels(sl[0..i]) + vowels(seq![sl@[i]])
                vowels_concat(sl[0..i], seq![sl@[i]]);
                vowels_single(sl@[i]);
                assert(vowels(sl[0..i+1]) == vowels(sl[0..i]) + vowels(seq![sl@[i]]));
                // since is_vowel(sl@[i]) is true, vowels(seq![sl@[i]]).len() == 1
                assert(vowels(seq![sl@[i]]) == seq![sl@[i]]);
                assert(vowels(seq![sl@[i]]).len() == 1);
                assert(vowels(sl[0..i+1]).len() == vowels(sl[0..i]).len() + 1);
                assert(vowels(sl[0..i+1]).len() == prev + 1);
                assert(count == vowels(sl[0..i+1]).len());
            }
        } else {
            let prev = count;
            // count unchanged
            proof {
                assert(prev == vowels(sl[0..i]).len());
                vowels_concat(sl[0..i], seq![sl@[i]]);
                vowels_single(sl@[i]);
                assert(vowels(seq![sl@[i]]) == seq![]);
                assert(vowels(seq![sl@[i]]).len() == 0);
                assert(vowels(sl[0..i+1]).len() == vowels(sl[0..i]).len() + 0);
                assert(prev == vowels(sl[0..i+1]).len());
            }
        }
        i = i + 1;
        // maintain invariant for next iteration
        assert(count == vowels(sl[0..i]).len());
    }
    // After loop, count == vowels(sl).len()
    assert(count == vowels(sl).len());
    let add: nat = if sl.len() > 0 && (sl.last() == 'y' || sl.last() == 'Y') { 1 } else { 0 };
    let total_u32: u32 = (count + add) as u32;
    ret = total_u32;
    proof {
        // Show the postcondition holds
        assert(count == vowels(sl).len());
        assert(inner_expr_vowels_count(s, ret));
    }
}
// </vc-code>

fn main() {}
}