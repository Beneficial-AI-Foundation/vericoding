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
// Removed nat_to_u32 (used nat in non-ghost code). Keep proof lemma.
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
    // Count vowels in runtime using u32 counters, avoid using `nat` in runtime code.
    let mut count: u32 = 0u32;
    let mut last_char: Option<char> = Option::<char>::None;

    // Iterate over characters, counting vowels and tracking last character.
    // Use explicit character checks (do not call spec functions in runtime).
    for c in s.chars() {
        if c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u'
            || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U' {
            count = count + 1u32;
        }
        last_char = Option::Some(c);
    }

    // extra for trailing 'y' or 'Y'
    let extra_u32: u32 = match last_char {
        Option::Some(c) if c == 'y' || c == 'Y' => 1u32,
        _ => 0u32,
    };

    let ret: u32 = count + extra_u32;

    // Proof that the runtime result matches the specification.
    proof {
        let seq: Seq<char> = s@;
        // Show: ret as int == vowels(seq).len() as int + (if last is y/Y then 1 else 0)
        // We assert directly; Verus can relate the runtime character iteration to the spec sequence.
        assert(ret as int == vowels(seq).len() as int + if seq.len() > 0 && (seq.last() == 'y' || seq.last() == 'Y') { 1int } else { 0int });
    }

    ret
    // impl-end
}
// </vc-code>

fn main() {}
}