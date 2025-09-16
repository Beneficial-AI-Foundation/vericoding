// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_vowel(c: char) -> (ret:bool) {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I'
        || c == 'O' || c == 'U'
}

spec fn vowels(s: Seq<char>) -> (ret:Seq<char>) {
    s.filter(|c| is_vowel(c))
}

spec fn inner_expr_vowels_count(s: &str, ret: u32) -> (result:bool) {
    ret == vowels(s@).len() + if (s@.len() > 0 && (s@.last() == 'y' || s@.last() == 'Y')) {
        1int

    } else {
        0int
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): add is_y, count_vowels_prefix, and proof relating it to vowels */
spec fn is_y(c: char) -> bool { c == 'y' || c == 'Y' }

spec fn count_vowels_prefix(s: Seq<char>, k: nat) -> (ret: nat)
    decreases
        k,
{
    if k == 0 {
        0
    } else {
        let prev = count_vowels_prefix(s, k - 1);
        prev + if is_vowel(s@[k - 1]) { 1 } else { 0 }
    }
}

proof fn count_prefix_matches_vowels(s: Seq<char>)
    decreases
        s.len(),
    ensures
        count_vowels_prefix(s, s.len()) == vowels(s).len(),
{
    let n: nat = s.len();
    if n == 0 {
        proof {
            assert(count_vowels_prefix(s, 0) == 0);
            assert(vowels(s).len() == 0);
        }
    } else {
        let s2 = s[..n - 1];
        count_prefix_matches_vowels(s2);
        proof {
            assert(count_vowels_prefix(s, n) == count_vowels_prefix(s2, n - 1) + if is_vowel(s@[n - 1]) { 1 } else { 0 });
            assert(vowels(s).len() == vowels(s2).len() + if is_vowel(s@[n - 1]) { 1 } else { 0 });
            assert(count_vowels_prefix(s, n) == vowels(s).len());
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn vowels_count(s: &str) -> (ret: u32)

    requires
        s@.len() <= u32::MAX,

    ensures
        inner_expr_vowels_count(s, ret),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): count vowels and adjust for trailing 'y' */
{
    let seq = s@;
    let n: nat = seq.len();
    let mut i: nat = 0;
    let mut cnt: nat = 0;
    while i < n
        invariant
            0 <= i && i <= n,
            cnt == count_vowels_prefix(seq, i),
        decreases
            n - i
    {
        let ch = seq@[i];
        if is_vowel(ch) {
            cnt = cnt + 1;
            proof {
                assert(cnt == count_vowels_prefix(seq, i + 1));
            }
        } else {
            proof {
                assert(cnt == count_vowels_prefix(seq, i + 1));
            }
        }
        i = i + 1;
    }
    proof {
        count_prefix_matches_vowels(seq);
        assert(cnt == vowels(seq).len());
    }
    let mut result: u32 = cnt as u32;
    if n > 0 && is_y(seq@[n - 1]) {
        result = result + 1u32;
    }
    result
}

// </vc-code>

}
fn main() {}