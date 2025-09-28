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
/* helper modified by LLM (iteration 5): fixed syntax from 'lemma fn' to 'proof fn' */
#[verifier::spinoff_prover]
proof fn lemma_count_vowels_is_nonnegative(s: Seq<char>)
    ensures
        count_vowels(s) >= 0,
    decreases s.len()
{
    if s.len() > 0 {
        lemma_count_vowels_is_nonnegative(s.subrange(1, s.len() as int));
    }
}

/* helper modified by LLM (iteration 5): fixed syntax from 'lemma fn' to 'proof fn' */
#[verifier::spinoff_prover]
proof fn lemma_count_vowels_distributive(s1: Seq<char>, s2: Seq<char>)
    ensures
        count_vowels(s1 + s2) == count_vowels(s1) + count_vowels(s2),
    decreases s1.len()
{
    if s1.len() > 0 {
        lemma_count_vowels_distributive(s1.subrange(1, s1.len() as int), s2);
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
    /* code modified by LLM (iteration 5): added proofs for loop invariants and post-loop logic */
    let mut count: u8 = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            count as int == count_vowels(s@.subrange(0, i as int)),
            (count_vowels(s@) + (if s@.len() > 0 && s@[s@.len() - 1] == 'y' { 1int } else { 0int })) <= u8::MAX as int,
        decreases s.len() - i
    {
        proof {
            lemma_count_vowels_distributive(s@.subrange(0, i as int), seq![s@[i as int]]);

            let next_prefix = s@.subrange(0, (i + 1) as int);
            let suffix = s@.subrange((i + 1) as int, s@.len() as int);
            lemma_count_vowels_distributive(next_prefix, suffix);
            lemma_count_vowels_is_nonnegative(suffix);
        }

        if is_vowel(s[i]) {
            count = count + 1;
        }
        i = i + 1;
    }

    if s.len() > 0 && s[s.len() - 1] == 'y' {
        count = count + 1;
    }
    
    count
}

// </vc-code>


}

fn main() {}