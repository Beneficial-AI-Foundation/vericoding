use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn is_digit(c: char) -> bool {
    c == '0' || c == '1' || c == '2' || c == '3' || c == '4' || 
    c == '5' || c == '6' || c == '7' || c == '8' || c == '9'
}

fn allDigits(s: Seq<char>) -> (result: bool)
    ensures
        result <==> (forall i: int :: 0 <= i < s.len() ==> is_digit(s[i]))
{
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall j: int :: 0 <= j < i ==> is_digit(s[j])
    {
        let c = s[i as int];
        
        if !is_digit(c) {
            // At this point we know !is_digit(s[i as int])
            // and i < s.len(), so we have a counterexample
            assert(!is_digit(s[i as int]) && 0 <= i < s.len());
            assert(exists k: int :: 0 <= k < s.len() && !is_digit(s[k])) by {
                // Witness: k = i as int
            }
            return false;
        }
        i = i + 1;
    }
    
    // When we exit the loop, i == s.len() and the invariant tells us
    // forall j: int :: 0 <= j < i ==> is_digit(s[j])
    // Since i == s.len(), this means forall j: int :: 0 <= j < s.len() ==> is_digit(s[j])
    assert(i == s.len());
    assert(forall j: int :: 0 <= j < s.len() ==> is_digit(s[j]));
    return true;
}

}