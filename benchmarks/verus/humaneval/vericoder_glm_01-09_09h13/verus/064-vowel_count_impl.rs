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
proof fn lemma_vowels_append(s: Seq<char>, c: char)
    ensures
        vowels(s.push(c)) == if (is_vowel(c)) { vowels(s).push(c) } else { vowels(s) }
{
    lemma_filter_append(s, Seq::singleton(c), |c: char| is_vowel(c));
    let single = Seq::singleton(c);
    assert(vowels(single) == if is_vowel(c) { single } else { Seq::empty() });
    if is_vowel(c) {
        assert(vowels(s.push(c)) == vowels(s) + single);
        assert(vowels(s) + single == vowels(s).push(c));
    } else {
        assert(vowels(s.push(c)) == vowels(s) + Seq::empty());
        assert(vowels(s) + Seq::empty() == vowels(s));
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
    let mut count: u32 = 0u32;
    let n = s.len();

    for i in 0..n
        invariant
            n == s@.len(),
            s@.len() <= u32::MAX,
            count <= s@.len(),
            count == vowels(s@.take(i as nat)).len(),
    {
        let c = s@.index(i as nat);

        if is_vowel(c) {
            count = count + 1;
        }
        proof {
            assert(s@.take((i + 1) as nat) == s@.take(i as nat).push(c));
            lemma_vowels_append(s@.take(i as nat), c);
            assert(vowels(s@.take((i + 1) as nat)).len() == vowels(s@.take(i as nat)).len() + if is_vowel(c) { 1 } else { 0 });
        }
    }

    if n > 0 {
        proof {
            assert(s@.index((n - 1) as nat) == s@.last());
        }
        if s@.last() == 'y' || s@.last() == 'Y' {
            count = count + 1;
        }
    }

    proof {
        reveal(inner_expr_vowels_count);
        let cond = s@.len() > 0 && (s@.last() == 'y' || s@.last() == 'Y');
        if cond {
            assert(count == vowels(s@).len() + 1);
        } else {
            assert(count == vowels(s@).len());
        }
        assert(inner_expr_vowels_count(s, count));
    }

    count
}
// </vc-code>

fn main() {}
}