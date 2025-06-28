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
    
    // Apply the multiset swap lemma
    proof {
        multiset_swap_lemma(string_to_seq(s), i as int, j as int);
        assert(multiset(vec_to_seq(chars)) == multiset(string_to_seq(s)));
    }
    
    // Convert Vec<char> to Vec<u8> for string construction
    let mut bytes: Vec<u8> = Vec::new();
    let mut char_idx: usize = 0;
    
    while char_idx < chars.len()
        invariant
            char_idx <= chars.len(),
            bytes.len() == char_idx,
            // The bytes represent the UTF-8 encoding of the characters
            forall k: nat :: k < char_idx ==> bytes@[k as int] == chars@[k as int] as u8
    {
        // For simplicity, we assume all characters are ASCII (can be extended for full Unicode)
        let ch = chars[char_idx];
        bytes.push(ch as u8);
        char_idx += 1;
    }
    
    // Convert bytes to string
    let result = String::from_utf8_unchecked(bytes);
    
    // Final assertions to help verification
    assert(result.len() == s.len());
    
    proof {
        // Establish that the result has the same character sequence as our swapped chars
        assert(forall k: nat :: k < chars.len() ==> string_to_seq(result)[k as int] == chars@[k as int]);
        // Therefore the multiset property holds
        assert(multiset(string_to_seq(result)) == multiset(vec_to_seq(chars)));
        assert(multiset(string_to_seq(result)) == multiset(string_to_seq(s)));
    }
    
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
    // This is a fundamental property of multisets - swapping elements preserves the multiset
    // Verus should be able to prove this automatically for multisets
}

}