use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn StringSwap(s: String, i: nat, j: nat) -> (t: String)
    requires
        i >= 0 && j >= 0 && s.len() >= 0,
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
            forall k: nat :: k < idx ==> chars.spec_index(k as int) == s.spec_index(k)
    {
        chars.push(s.spec_index(idx as nat));
        idx += 1;
    }
    
    // Perform the swap
    let char_i = chars[i as usize];
    let char_j = chars[j as usize];
    chars.set(i as usize, char_j);
    chars.set(j as usize, char_i);
    
    // Convert back to string
    let result = String::from_iter(chars.spec_index(..));
    
    assert(result.len() == s.len());
    assert(multiset(result.spec_index(..)) == multiset(s.spec_index(..)));
    assert(forall k:nat :: k != i && k != j && k < s.len() ==> result.spec_index(k) == s.spec_index(k));
    assert(result.spec_index(i) == s.spec_index(j) && result.spec_index(j) == s.spec_index(i));
    
    result
}

}