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
fn nat_to_u32(n: nat) -> (r: u32)
    requires
        n <= u32::MAX,
    ensures
        r as int == n as int
{
    if n == (0 as nat) {
        0u32
    } else {
        1u32 + nat_to_u32(n - (1 as nat))
    }
}

proof fn lemma_total_le_len(seq: Seq<char>) {
    // Show: vowels(seq).len() + (if last is 'y'/'Y' then 1 else 0) <= seq.len()
    let base: nat = vowels(seq).len();
    let extra: nat = if seq.len() > (0 as nat) && (seq.last() == 'y' || seq.last() == 'Y') { 1 as nat } else { 0 as nat };

    if seq.len() == (0 as nat) {
        // base == 0 and extra == 0
        assert(base == (0 as nat));
        assert(extra == (0 as nat));
        assert(base + extra == (0 as nat));
    } else {
        if seq.last() == 'y' || seq.last() == 'Y' {
            // last char is not a vowel, so the number of vowels is strictly less than the length
            // hence base <= seq.len() - 1
            // Prove base < seq.len():
            // if base == seq.len() then every element would be a vowel, contradicting last not a vowel
            assert(!(base == seq.len())); // since last char not vowel
            // from !(base == seq.len()) and base <= seq.len(), we get base <= seq.len() - 1
            assert(base <= seq.len());
            assert(base + (1 as nat) <= seq.len());
            assert(base + extra <= seq.len());
        } else {
            // extra == 0, and base <= seq.len()
            assert(extra == (0 as nat));
            assert(base <= seq.len());
            assert(base + extra <= seq.len());
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
    // impl-start
    let seq: Seq<char> = s@;
    let base: nat = vowels(seq).len();
    let extra: nat = if seq.len() > (0 as nat) && (seq.last() == 'y' || seq.last() == 'Y') { 1 as nat } else { 0 as nat };
    let total: nat = base + extra;

    // total <= seq.len() by lemma, and seq.len() <= u32::MAX by precondition, so total <= u32::MAX
    proof {
        lemma_total_le_len(seq);
        assert(total <= seq.len());
        assert(seq.len() <= u32::MAX);
        assert(total <= u32::MAX);
    }

    nat_to_u32(total)
    // impl-end
}
// </vc-code>

fn main() {}
}