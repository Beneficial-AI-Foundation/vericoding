use vstd::prelude::*;

verus! {

spec fn is_vowel(c: char) -> bool {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' ||
    c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}

// <vc-helpers>
spec fn count_vowel_neighbors_spec(s: Seq<char>) -> nat {
    Set::new(|i: int| 1 <= i < s.len() - 1 && 
              is_vowel(s[i-1]) && 
              is_vowel(s[i+1])).len()
}

proof fn lemma_count_bounded(s: Seq<char>) 
    ensures count_vowel_neighbors_spec(s) <= s.len()
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn count_vowel_neighbors(s: &str) -> (count: usize)
    ensures 
        count >= 0 &&
        count == Set::new(|i: int| 1 <= i < s@.len() - 1 && 
                          is_vowel(s@[i-1]) && 
                          is_vowel(s@[i+1])).len(),
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    if s@.len() < 3 {
        return 0;
    }
    
    let mut count: usize = 0;
    let mut i: usize = 1;
    
    while i < (s@.len() - 1) as usize
        invariant 
            1 <= i <= s@.len() - 1,
            count == Set::new(|j: int| 1 <= j < i && 
                             is_vowel(s@[j-1]) && 
                             is_vowel(s@[j+1])).len(),
    {
        if is_vowel(s@[i-1]) && is_vowel(s@[i+1]) {
            count = count + 1;
        }
        i = i + 1;
    }
    
    proof {
        assert(i == (s@.len() - 1) as usize);
        assert(count == Set::new(|j: int| 1 <= j < s@.len() - 1 && 
                                is_vowel(s@[j-1]) && 
                                is_vowel(s@[j+1])).len());
    }
    
    count
}
// </vc-code>

fn main() {
}

}