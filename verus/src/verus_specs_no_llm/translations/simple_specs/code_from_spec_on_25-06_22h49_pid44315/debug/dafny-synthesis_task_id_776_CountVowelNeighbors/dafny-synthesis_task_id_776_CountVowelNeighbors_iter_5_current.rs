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

fn count_vowel_neighbors(s: String) -> (count: usize)
    ensures
        count as int == (set i: int | 1 <= i < s.len()-1 && s.len() >= 3 && IsVowel(s.as_bytes().spec_index(i-1)) && IsVowel(s.as_bytes().spec_index(i+1))).len(),
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
            count as int == (set j: int | 1 <= j < i && IsVowel(s.as_bytes().spec_index(j-1)) && IsVowel(s.as_bytes().spec_index(j+1))).len(),
    {
        let prev_char = s.as_bytes()[i-1];
        let next_char = s.as_bytes()[i+1];
        
        if is_vowel_exec(prev_char) && is_vowel_exec(next_char) {
            count = count + 1;
        }
        i = i + 1;
    }
    
    count
}

}