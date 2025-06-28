use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn StringSwap(s: String, i: nat, j: nat) -> (t: String)
    requires
        s.len() > 0 ==> i < s.len() && j < s.len()
    ensures
        multiset(s.spec_index(..)) == multiset(t.spec_index(..)),
        s.len() == t.len(),
        s.len() > 0 ==> forall k:nat :: k != i && k != j && k < s.len() ==> t.spec_index(k) == s.spec_index(k),
        s.len() > 0 ==> t.spec_index(i) == s.spec_index(j) && t.spec_index(j) == s.spec_index(i),
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
            forall k: nat :: k < idx ==> chars[k as int] == s.spec_index(k)
    {
        chars.push(s.spec_index(idx));
        idx += 1;
        
        proof {
            assert(chars.len() == idx);
            assert(chars[idx as int - 1] == s.spec_index(idx - 1));
        }
    }
    
    proof {
        assert(chars.len() == s.len());
        assert(forall k: nat :: k < s.len() ==> chars[k as int] == s.spec_index(k));
    }
    
    // Perform the swap
    let char_i = chars[i as int];
    let char_j = chars[j as int];
    chars.set(i as usize, char_j);
    chars.set(j as usize, char_i);
    
    proof {
        assert(chars[i as int] == char_j);
        assert(chars[j as int] == char_i);
        assert(char_i == s.spec_index(i));
        assert(char_j == s.spec_index(j));
    }
    
    // Convert back to string using a helper function
    let result = vec_to_string(chars);
    
    proof {
        assert(result.len() == chars.len());
        assert(result.len() == s.len());
        assert(forall k: nat :: k < result.len() ==> result.spec_index(k) == chars[k as int]);
        
        // Prove multiset equality
        assert(multiset(result.spec_index(..)) == multiset(chars.spec_index(..)));
        assert(multiset(chars.spec_index(..)) == multiset(s.spec_index(..)));
        
        // Prove character preservation
        assert(forall k:nat :: k != i && k != j && k < s.len() ==> result.spec_index(k) == chars[k as int]);
        assert(forall k:nat :: k != i && k != j && k < s.len() ==> chars[k as int] == s.spec_index(k));
        
        // Prove swap correctness
        assert(result.spec_index(i) == chars[i as int]);
        assert(result.spec_index(j) == chars[j as int]);
        assert(chars[i as int] == char_j);
        assert(chars[j as int] == char_i);
        assert(char_j == s.spec_index(j));
        assert(char_i == s.spec_index(i));
    }
    
    result
}

// Helper function to convert Vec<char> to String
fn vec_to_string(chars: Vec<char>) -> (result: String)
    ensures
        result.len() == chars.len(),
        forall k: nat :: k < chars.len() ==> result.spec_index(k) == chars[k as int]
{
    let mut result = String::new();
    let mut i: usize = 0;
    
    while i < chars.len()
        invariant
            i <= chars.len(),
            result.len() == i,
            forall k: nat :: k < i ==> result.spec_index(k) == chars[k as int]
    {
        result.push(chars[i]);
        i += 1;
        
        proof {
            assert(result.len() == i);
            assert(result.spec_index(i - 1) == chars[i as int - 1]);
        }
    }
    
    proof {
        assert(result.len() == chars.len());
        assert(forall k: nat :: k < chars.len() ==> result.spec_index(k) == chars[k as int]);
    }
    
    result
}

}