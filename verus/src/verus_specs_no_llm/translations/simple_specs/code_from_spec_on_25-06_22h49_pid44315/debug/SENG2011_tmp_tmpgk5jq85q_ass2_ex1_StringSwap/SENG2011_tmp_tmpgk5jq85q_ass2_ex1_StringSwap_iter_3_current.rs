use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn string_to_seq(s: String) -> Seq<char> {
    s@
}

spec fn vec_to_seq(v: Vec<char>) -> Seq<char> {
    v@
}

fn StringSwap(s: String, i: nat, j: nat) -> (t: String)
    requires
        s.len() > 0 ==> i < s.len() && j < s.len()
    ensures
        multiset(string_to_seq(s)) == multiset(string_to_seq(t)),
        s.len() == t.len(),
        s.len() > 0 ==> forall k:nat :: k != i && k != j && k < s.len() ==> string_to_seq(t)[k as int] == string_to_seq(s)[k as int],
        s.len() > 0 ==> string_to_seq(t)[i as int] == string_to_seq(s)[j as int] && string_to_seq(t)[j as int] == string_to_seq(s)[i as int],
        s.len() == 0 ==> t == s
{
    if s.len() == 0 {
        return s;
    }
    
    let mut chars: Vec<char> = Vec::new();
    let mut idx: usize = 0;
    
    while idx < s.len()
        invariant
            idx <= s.len(),
            chars.len() == idx,
            forall k: nat :: k < idx ==> chars@[k as int] == string_to_seq(s)[k as int]
    {
        let ch = s.get_char(idx);
        chars.push(ch);
        idx += 1;
    }
    
    // Perform the swap
    let char_i = chars[i as int];
    let char_j = chars[j as int];
    chars.set(i as usize, char_j);
    chars.set(j as usize, char_i);
    
    // Convert back to string using a helper function
    let result = vec_to_string(chars);
    
    result
}

// Helper function to convert Vec<char> to String
fn vec_to_string(chars: Vec<char>) -> (result: String)
    ensures
        result.len() == chars.len(),
        forall k: nat :: k < chars.len() ==> string_to_seq(result)[k as int] == chars@[k as int]
{
    let mut result = String::new();
    let mut i: usize = 0;
    
    while i < chars.len()
        invariant
            i <= chars.len(),
            result.len() == i,
            forall k: nat :: k < i ==> string_to_seq(result)[k as int] == chars@[k as int]
    {
        result.push(chars[i]);
        i += 1;
    }
    
    result
}

}