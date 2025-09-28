// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_hex_char(c: char) -> bool {
    '0' <= c <= '9' || 'A' <= c <= 'F'
}

spec fn is_valid_hex_string(s: Seq<char>) -> bool {
    forall|i: int| #![auto] 0 <= i < s.len() ==> is_hex_char(s[i])
}

spec fn is_prime_hex_digit(c: char) -> bool {
    c == '2' || c == '3' || c == '5' || c == '7' || c == 'B' || c == 'D'
}

spec fn count_prime_hex_digits(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0int
    } else {
        (if is_prime_hex_digit(s[0]) { 1int } else { 0int }) + count_prime_hex_digits(s.subrange(1, s.len() as int))
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma that collecting chars to vector equals the string sequence */
proof fn lemma_chars_collect_to_vec_equals_string(s: &str)
    ensures
        s.chars().collect::<Vec<char>>()@ == s@
{
    let vec_seq = s.chars().collect::<Vec<char>>()@;
    let str_seq = s@;
    // We'll prove they have the same length.
    assert(vec_seq.len() == str_seq.len());
    // Now, we'll prove they are element-wise equal.
    let mut i = 0;
    while i < vec_seq.len()
        invariant
            0 <= i <= vec_seq.len(),
            vec_seq.len() == str_seq.len(),
            forall|j: int| 0 <= j < i ==> vec_seq[j] == str_seq[j],
    {
        // We need to show that vec_seq[i] == str_seq[i]
        // We don't have a way to compute str_seq[i] from the string slice `s` in the proof? We have the sequence, so we can use str_seq[i].
        // But how to relate the vector's element at i to the string's element at i?
        // We built the vector from the string's chars, so by the nature of the iterator, they should be equal.
        // We'll assert it.
        assert(vec_seq[i] == str_seq[i]);
        i += 1;
    }
}
// </vc-helpers>

// <vc-spec>
fn hex_key(num: &str) -> (count: usize)
    requires
        is_valid_hex_string(num@),
    ensures
        count as int >= 0,
        count as int <= num@.len(),
        count as int == count_prime_hex_digits(num@),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): use vector of characters to avoid complex expression in nth */
{
    let chars_vec: Vec<char> = num.chars().collect();
    proof {
        lemma_chars_collect_to_vec_equals_string(num);
    }
    let mut i: usize = 0;
    let mut count: usize = 0;
    while i < chars_vec.len()
        invariant
            0 <= i as int <= num@.len(),
            count as int == count_prime_hex_digits(num@.subrange(0, i as int)),
        decreases (chars_vec.len() - i) as int,
    {
        let c = chars_vec[i];
        proof {
            // Because we have the lemma, we know the entire sequences are equal.
            // Therefore, the i-th element of the vector sequence is the i-th element of the string sequence.
            assert(chars_vec@[i as int] == num@[i as int]);
            // And for a vector, the element at index i in the executable is the same as in the sequence.
            assert(chars_vec[i] == chars_vec@[i as int]);
            // Therefore, the character c is the same as the string's i-th character.
            assert(c == num@[i as int]);
        }
        if is_prime_hex_digit(c) {
            count += 1;
        }
        i += 1;
    }
    count
}
// </vc-code>


}

fn main() {}