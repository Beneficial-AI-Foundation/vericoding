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
proof fn lemma_count_vowels_recursive(s: Seq<char>, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        count_vowels(s) == count_vowels(s.subrange(0, i)) + count_vowels(s.subrange(i, s.len() as int)),
    decreases s.len() - i
{
    if i < s.len() as int {
        lemma_count_vowels_recursive(s.subrange(1, s.len() as int), i - 1);
    }
}

proof fn lemma_count_vowels_single_char(c: char)
    ensures
        count_vowels(Seq::new(1, |i: int| c)) == (if is_vowel(c) { 1int } else { 0int })
{
}

proof fn lemma_count_vowels_empty()
    ensures
        count_vowels(Seq::empty()) == 0int
{
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
    /* code modified by LLM (iteration 5): Fixed type casting and ghost type annotations */
    let mut count: u8 = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            count as int == count_vowels(s@.subrange(0, i as int)),
    {
        let c = s[i];
        if is_vowel(c) {
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