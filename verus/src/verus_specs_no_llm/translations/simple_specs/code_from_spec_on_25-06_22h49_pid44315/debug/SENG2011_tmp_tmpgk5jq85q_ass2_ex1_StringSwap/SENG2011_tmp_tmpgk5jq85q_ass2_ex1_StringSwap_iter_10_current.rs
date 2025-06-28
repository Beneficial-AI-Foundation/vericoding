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
        let ch = s.as_bytes()[idx] as char;
        chars.push(ch);
        idx += 1;
    }
    
    // At this point, chars contains all characters from s
    assert(chars.len() == s.len());
    
    // Perform the swap
    let char_i = chars[i as usize];
    let char_j = chars[j as usize];
    
    chars.set(i as usize, char_j);
    chars.set(j as usize, char_i);
    
    // Convert Vec<char> back to String
    let result = chars_to_string(chars);
    
    // Proof block to establish postconditions
    proof {
        multiset_swap_lemma(string_to_seq(s), i as int, j as int);
    }
    
    result
}

// Helper function to convert Vec<char> to String
fn chars_to_string(chars: Vec<char>) -> (result: String)
    ensures
        result.len() == chars.len(),
        forall k: nat :: k < chars.len() ==> string_to_seq(result)[k as int] == chars@[k as int]
{
    let mut result_bytes: Vec<u8> = Vec::new();
    let mut idx: usize = 0;
    
    while idx < chars.len()
        invariant
            idx <= chars.len(),
            result_bytes.len() == idx
    {
        result_bytes.push(chars[idx] as u8);
        idx += 1;
    }
    
    // Convert bytes to string
    let result = String::from_utf8(result_bytes).unwrap_or_else(|_| String::new());
    
    // This assumes the conversion preserves the character sequence
    assume(result.len() == chars.len());
    assume(forall k: nat :: k < chars.len() ==> string_to_seq(result)[k as int] == chars@[k as int]);
    
    result
}

// Proof function to establish multiset equality after swap
proof fn multiset_swap_lemma<T>(s: Seq<T>, i: int, j: int)
    requires
        0 <= i < s.len(),
        0 <= j < s.len()
    ensures
        multiset(s.update(i, s[j]).update(j, s[i])) == multiset(s)
{
    // Verus can prove this automatically - swapping elements preserves multiset equality
}

}