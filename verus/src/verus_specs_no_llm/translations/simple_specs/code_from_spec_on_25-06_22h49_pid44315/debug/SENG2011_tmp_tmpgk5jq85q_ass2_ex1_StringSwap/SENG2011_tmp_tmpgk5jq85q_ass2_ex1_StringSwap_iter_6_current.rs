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
    
    // Convert string to Vec<char>
    while idx < s.len()
        invariant
            idx <= s.len(),
            chars.len() == idx,
            forall k: nat :: k < idx ==> chars@[k as int] == string_to_seq(s)[k as int]
    {
        let ch = string_to_seq(s)[idx as int];
        chars.push(ch);
        idx += 1;
    }
    
    // At this point, chars contains all characters from s
    assert(chars.len() == s.len());
    assert(forall k: nat :: k < s.len() ==> chars@[k as int] == string_to_seq(s)[k as int]);
    
    // Perform the swap
    let char_i = chars[i as usize];
    let char_j = chars[j as usize];
    
    // Update the characters in place
    chars.set(i as usize, char_j);
    chars.set(j as usize, char_i);
    
    // Prove multiset property
    assert(chars.len() == s.len());
    
    // Convert back to string
    let result = vec_to_string(chars);
    
    // Final assertions to help verification
    assert(result.len() == s.len());
    assert(multiset(string_to_seq(result)) == multiset(string_to_seq(s)));
    
    result
}

// Helper function to convert Vec<char> to String
fn vec_to_string(chars: Vec<char>) -> (result: String)
    ensures
        result.len() == chars.len(),
        forall k: nat :: k < chars.len() ==> string_to_seq(result)[k as int] == chars@[k as int]
{
    // Use new_strlit for string construction in Verus
    let mut result_string = new_strlit("");
    let mut i: usize = 0;
    
    while i < chars.len()
        invariant
            i <= chars.len(),
            result_string.len() == i,
            forall k: nat :: k < i ==> string_to_seq(result_string)[k as int] == chars@[k as int]
    {
        let ch = chars[i];
        result_string = string_push(result_string, ch);
        i += 1;
    }
    
    result_string
}

// Helper function to push a character to a string
fn string_push(s: String, c: char) -> (result: String)
    ensures
        result.len() == s.len() + 1,
        forall k: nat :: k < s.len() ==> string_to_seq(result)[k as int] == string_to_seq(s)[k as int],
        string_to_seq(result)[s.len() as int] == c
{
    // In Verus, we can construct strings by concatenation
    let char_str = new_strlit("") + c;  // Convert char to string
    s + char_str
}

}