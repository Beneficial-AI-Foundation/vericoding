// <vc-preamble>
use vstd::prelude::*;
use vstd::multiset::*;

verus! {

proof fn to_multiset(s: &str) -> (mset: Multiset<char>)
    ensures mset == s@.to_multiset()
{
    assume(false);
    s@.to_multiset()
}

proof fn mset_equal(s: Multiset<char>, t: Multiset<char>) -> (equal: bool)
    ensures s == t <==> equal
{
    assume(false);
    true
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Switched from sorting to frequency map approach and added proof for invariant. */
fn get_char_counts(s: &str) -> (counts: Map<char, nat>)
    ensures
        counts == s@.to_multiset().to_map(),
{
    let mut counts = Map::<char, nat>::new();
    let mut i: u64 = 0;
    while i < s.char_len()
        invariant
            i <= s.char_len(),
            counts == s@.subrange(0, i as int).to_multiset().to_map(),
        decreases s.char_len() - i
    {
        let ch = s.get_char(i);

        proof {
            let s_sub = s@.subrange(0, i as int);
            let m_sub = s_sub.to_multiset();
            vstd::multiset::lemma_to_map_insert(m_sub, ch);
        }

        let count = if counts.contains_key(ch) { counts.index(ch) } else { 0 };
        counts = counts.insert(ch, (count + 1) as nat);
        i = i + 1;
    }
    counts
}
// </vc-helpers>

// <vc-spec>
fn is_anagram(s: &str, t: &str) -> (equal: bool)
    ensures (s@.to_multiset() == t@.to_multiset()) == equal
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Switched from sorting to a frequency map approach to avoid unavailable dependencies. */
    if s.char_len() != t.char_len() {
        return false;
    }

    let s_counts = get_char_counts(s);
    let t_counts = get_char_counts(t);

    proof {
        vstd::multiset::lemma_multiset_eq_to_map(s@.to_multiset(), t@.to_multiset());
    }

    s_counts == t_counts
}
// </vc-code>

}
fn main() {}