use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn FindFirstRepeatedChar(s: String) -> (found: bool, c: char)
    ensures
        found ==> exists i, j :: 0 <= i < j < s.as_bytes().len() && s.as_bytes().spec_index(i) == s.as_bytes().spec_index(j) && s.as_bytes().spec_index(i) == c as u8 && (forall k, l :: 0 <= k < l < j && s.as_bytes().spec_index(k) == s.as_bytes().spec_index(l) ==> k >= i),
        !found ==> (forall i, j :: 0 <= i < j < s.as_bytes().len() ==> s.as_bytes().spec_index(i) != s.as_bytes().spec_index(j))
{
    let s_chars = s.as_bytes();
    let mut i = 0;
    
    while i < s_chars.len()
        invariant
            0 <= i <= s_chars.len(),
            forall k, l :: 0 <= k < l < i ==> s.as_bytes().spec_index(k) != s.as_bytes().spec_index(l)
    {
        let mut j = i + 1;
        while j < s_chars.len()
            invariant
                i < j <= s_chars.len(),
                forall k, l :: 0 <= k < l < i ==> s.as_bytes().spec_index(k) != s.as_bytes().spec_index(l),
                forall l :: i < l < j ==> s.as_bytes().spec_index(i) != s.as_bytes().spec_index(l)
        {
            if s_chars[i] == s_chars[j] {
                assert(s.as_bytes().spec_index(i) == s.as_bytes().spec_index(j));
                assert(s.as_bytes().spec_index(i) == s_chars[i]);
                return (true, s_chars[i] as char);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    
    assert(forall i, j :: 0 <= i < j < s.as_bytes().len() ==> s.as_bytes().spec_index(i) != s.as_bytes().spec_index(j));
    return (false, '\0');
}

}