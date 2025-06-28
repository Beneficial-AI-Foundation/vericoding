use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn StartAndEndWithSameChar(s: &str) -> (result: bool)
    requires
        s.len() > 0
    ensures
        result <==> s@.index(0) == s@.index(s@.len() - 1)
{
    let chars: Vec<char> = s.chars().collect();
    let first_char = chars[0];
    let last_char = chars[chars.len() - 1];
    
    let result = first_char == last_char;
    
    proof {
        // We need to establish the relationship between the collected chars
        // and the original string's character sequence
        assert(chars@.len() == s@.len());
        assert(chars@[0] == s@.index(0));
        assert(chars@[chars@.len() - 1] == s@.index(s@.len() - 1));
        assert(result == (first_char == last_char));
        assert(first_char == chars@[0]);
        assert(last_char == chars@[chars@.len() - 1]);
        assert(result == (chars@[0] == chars@[chars@.len() - 1]));
        assert(result == (s@.index(0) == s@.index(s@.len() - 1)));
    }
    
    result
}

}