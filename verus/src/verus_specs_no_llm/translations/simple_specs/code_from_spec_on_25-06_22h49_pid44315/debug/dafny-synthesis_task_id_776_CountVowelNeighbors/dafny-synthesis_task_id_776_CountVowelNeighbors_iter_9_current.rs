use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsVowel(c: u8) -> bool {
    c == ('a' as u8) || c == ('e' as u8) || c == ('i' as u8) || c == ('o' as u8) || c == ('u' as u8) || 
    c == ('A' as u8) || c == ('E' as u8) || c == ('I' as u8) || c == ('O' as u8) || c == ('U' as u8)
}

fn is_vowel_exec(c: u8) -> (result: bool)
    ensures result == IsVowel(c)
{
    c == ('a' as u8) || c == ('e' as u8) || c == ('i' as u8) || c == ('o' as u8) || c == ('u' as u8) || 
    c == ('A' as u8) || c == ('E' as u8) || c == ('I' as u8) || c == ('O' as u8) || c == ('U' as u8)
}

spec fn count_vowel_neighbors_spec(s: Seq<u8>, start: int, end: int) -> int
    decreases end - start
{
    if start >= end {
        0
    } else {
        let current_count = if start >= 1 && start < s.len() - 1 && 
                              IsVowel(s[start - 1]) && IsVowel(s[start + 1]) { 1 } else { 0 };
        current_count + count_vowel_neighbors_spec(s, start + 1, end)
    }
}

// Proof function to establish the recursive property
proof fn lemma_count_vowel_neighbors_recursive(s: Seq<u8>, start: int, end: int)
    requires start < end, start >= 1, start < s.len() - 1
    ensures count_vowel_neighbors_spec(s, start, end) == 
            (if IsVowel(s[start - 1]) && IsVowel(s[start + 1]) { 1 } else { 0 }) + 
            count_vowel_neighbors_spec(s, start + 1, end)
{
    // The proof follows directly from the definition
}

fn count_vowel_neighbors(s: String) -> (count: usize)
    ensures
        count as int == if s.len() >= 3 {
            count_vowel_neighbors_spec(s.as_bytes(), 1, (s.len() - 1) as int)
        } else {
            0
        },
{
    if s.len() < 3 {
        return 0;
    }
    
    let mut count: usize = 0;
    let mut i: usize = 1;
    
    while i < s.len() - 1
        invariant
            1 <= i <= s.len() - 1,
            s.len() >= 3,
            count as int == count_vowel_neighbors_spec(s.as_bytes(), 1, i as int),
    {
        let prev_char = s.as_bytes()[i-1];
        let next_char = s.as_bytes()[i+1];
        
        if is_vowel_exec(prev_char) && is_vowel_exec(next_char) {
            count = count + 1;
        }
        i = i + 1;
        
        // Use the lemma to help Verus understand the recursive relationship
        if i < s.len() {
            proof {
                lemma_count_vowel_neighbors_recursive(s.as_bytes(), i as int - 1, (s.len() - 1) as int);
            }
        }
    }
    
    count
}

}