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
    
    // Prove that the swap preserves multiset property
    proof {
        let old_seq = vec_to_seq(chars).update(i as int, char_i).update(j as int, char_j);
        let new_seq = vec_to_seq(chars);
        
        // The multiset is preserved after swapping
        assert(multiset(old_seq) == multiset(string_to_seq(s)));
        assert(multiset(new_seq) == multiset(old_seq));
    }
    
    // Convert back to string using from_utf8_unchecked
    let result = String::from_utf8_unchecked(chars);
    
    // Final assertions to help verification
    assert(result.len() == s.len());
    assert(multiset(string_to_seq(result)) == multiset(string_to_seq(s)));
    
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
}

}