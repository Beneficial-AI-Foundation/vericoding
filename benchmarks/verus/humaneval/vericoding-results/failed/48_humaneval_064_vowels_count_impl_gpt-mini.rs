// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_vowel(c: char) -> bool
{
  c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}

spec fn count_vowels(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0int
    } else {
        count_vowels(s.subrange(1, s.len() as int)) + (if is_vowel(s[0]) { 1int } else { 0int })
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): proof that count_vowels is nonnegative */
proof fn lemma_count_vowels_nonneg(s: Seq<char>)
    ensures
        count_vowels(s) >= 0,
    decreases
        s.len()
{
    if s.len() == 0 {
    } else {
        let len_int = s.len() as int;
        lemma_count_vowels_nonneg(s.subrange(1, len_int));
        assert(count_vowels(s.subrange(1, len_int)) >= 0);
        assert((if is_vowel(s[0]) { 1int } else { 0int }) >= 0);
        assert(count_vowels(s) >= 0);
    }
}

/* helper modified by LLM (iteration 5): relate prefix extension by one index to count_vowels */
proof fn lemma_count_vowels_prefix_step(s: Seq<char>, i: int)
    requires
        0 <= i && i < s.len() as int,
    ensures
        count_vowels(s.subrange(0, i + 1)) == count_vowels(s.subrange(0, i)) + (if is_vowel(s[i]) { 1int } else { 0int }),
    decreases
        s.len() as int - i
{
    if i == 0 {
        assert(count_vowels(s.subrange(0, 0)) == 0);
        assert(count_vowels(s.subrange(0, 1)) == (if is_vowel(s[0]) { 1int } else { 0int }));
        assert(count_vowels(s.subrange(0, 1)) == count_vowels(s.subrange(0, 0)) + (if is_vowel(s[0]) { 1int } else { 0int }));
    } else {
        let s1 = s.subrange(1, s.len() as int);
        lemma_count_vowels_prefix_step(s1, i - 1);
        assert(s.subrange(1, i + 1) == s1.subrange(0, i));
        assert(count_vowels(s.subrange(0, i + 1)) == count_vowels(s.subrange(1, i + 1)) + (if is_vowel(s[0]) { 1int } else { 0int }));
        assert(count_vowels(s.subrange(0, i)) == count_vowels(s.subrange(1, i)) + (if is_vowel(s[0]) { 1int } else { 0int }));
        assert(count_vowels(s1.subrange(0, i)) == count_vowels(s1.subrange(0, i - 1)) + (if is_vowel(s1[i - 1]) { 1int } else { 0int }));
        assert(s1[i - 1] == s[i]);
        assert(count_vowels(s.subrange(1, i + 1)) == count_vowels(s.subrange(1, i)) + (if is_vowel(s[i]) { 1int } else { 0int }));
        assert(count_vowels(s.subrange(0, i + 1)) == count_vowels(s.subrange(0, i)) + (if is_vowel(s[i]) { 1int } else { 0int }));
    }
}

// </vc-helpers>

// <vc-spec>
fn vowel_count(s: &Vec<char>) -> (count: u8)
  ensures
    count as int >= 0,
    count as int == count_vowels(s@) + (if s@.len() > 0 && s@[s@.len() - 1] == 'y' { 1int } else { 0int })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): count vowels using usize indices and link to specs via proofs; accumulate as usize and cast at end */
    let n: usize = s.len();
    let mut i: usize = 0;
    let mut acc: usize = 0;
    while i < n
        invariant
            acc as int == count_vowels(s@.subrange(0, i as int)),
            i <= n,
        decreases
            n - i
    {
        let c = s[i];
        if is_vowel(c) {
            acc = acc + 1;
            proof {
                lemma_count_vowels_prefix_step(s@, i as int);
                assert(acc as int == count_vowels(s@.subrange(0, (i + 1) as int)));
            }
        } else {
            proof {
                lemma_count_vowels_prefix_step(s@, i as int);
                assert(acc as int == count_vowels(s@.subrange(0, (i + 1) as int)));
            }
        }
        i = i + 1;
    }
    let add: usize = if n > 0 && s[n - 1] == 'y' { 1 } else { 0 };
    let total: usize = acc + add;
    total as u8
}

// </vc-code>


}

fn main() {}