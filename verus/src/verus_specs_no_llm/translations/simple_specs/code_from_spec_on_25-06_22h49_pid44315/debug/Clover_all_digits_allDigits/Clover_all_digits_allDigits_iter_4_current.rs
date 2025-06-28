use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn is_digit(c: char) -> bool {
    c == '0' || c == '1' || c == '2' || c == '3' || c == '4' || 
    c == '5' || c == '6' || c == '7' || c == '8' || c == '9'
}

fn allDigits(s: String) -> (result: bool)
    ensures
        result <==> (forall i: int :: 0 <= i < s.len() ==> is_digit(s.spec_index(i)))
{
    let chars: Vec<char> = s.chars().collect();
    
    // First establish the relationship between chars and string
    proof {
        assert(chars.len() == s.len());
        assert(forall i: int :: 0 <= i < chars.len() ==> chars.spec_index(i) == s.spec_index(i));
    }
    
    let mut i: usize = 0;
    while i < chars.len()
        invariant
            0 <= i <= chars.len(),
            chars.len() == s.len(),
            forall k: int :: 0 <= k < chars.len() ==> chars.spec_index(k) == s.spec_index(k),
            forall j: int :: 0 <= j < i ==> is_digit(s.spec_index(j))
    {
        let c = chars[i];
        
        proof {
            assert(c == chars.spec_index(i as int));
            assert(chars.spec_index(i as int) == s.spec_index(i as int));
            assert(c == s.spec_index(i as int));
        }
        
        if !is_digit(c) {
            proof {
                assert(!is_digit(s.spec_index(i as int)));
                assert(exists k: int :: 0 <= k < s.len() && !is_digit(s.spec_index(k)));
            }
            return false;
        }
        i = i + 1;
    }
    
    proof {
        assert(i == chars.len());
        assert(chars.len() == s.len());
        assert(forall j: int :: 0 <= j < s.len() ==> is_digit(s.spec_index(j)));
    }
    
    return true;
}

}