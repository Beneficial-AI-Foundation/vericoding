use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsVowel(c: char) -> bool {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || 
    c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}

fn is_vowel_exec(c: char) -> (result: bool)
    ensures result == IsVowel(c)
{
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || 
    c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}

fn CountVowelNeighbors(s: String) -> (count: usize)
    ensures
        count >= 0,
        count as int == (set i: int | 1 <= i < s.len()-1 && IsVowel(s.spec_index(i-1)) && IsVowel(s.spec_index(i+1))).len(),
{
    if s.len() < 3 {
        return 0;
    }
    
    let mut count: usize = 0;
    let mut i: usize = 1;
    
    while i < s.len() - 1
        invariant
            1 <= i <= s.len() - 1,
            count >= 0,
            count as int == (set j: int | 1 <= j < i && IsVowel(s.spec_index(j-1)) && IsVowel(s.spec_index(j+1))).len(),
    {
        let prev_char = s.spec_index((i-1) as int);
        let next_char = s.spec_index((i+1) as int);
        
        if is_vowel_exec(prev_char) && is_vowel_exec(next_char) {
            count = count + 1;
        }
        i = i + 1;
    }
    
    count
}

}