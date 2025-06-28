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
        s.len() == t.len(),
        s.len() == 0 ==> t == s,
        s.len() > 0 ==> t[i as int] == s[j as int] && t[j as int] == s[i as int],
        s.len() > 0 ==> forall|k: int| 0 <= k < s.len() && k != i && k != j ==> t[k] == s[k]
{
    if s.len() == 0 {
        s
    } else {
        let mut result = s.clone();
        let char_i = s[i as int];
        let char_j = s[j as int];
        
        // Convert to Vec<char> for easier manipulation
        let mut chars: Vec<char> = s.chars().collect();
        
        // Perform the swap
        chars.set(i as usize, char_j);
        chars.set(j as usize, char_i);
        
        // Convert back to String
        let swapped_string: String = chars.into_iter().collect();
        
        swapped_string
    }
}

method check(s: String, i: nat, j: nat) -> (result: int)
    requires
        i >= 0 && j >= 0 && s.len() >= 0,
        s.len() > 0 ==> i < s.len() && j < s.len()
{
    let t = StringSwap(s, i, j);
    
    assert(s.len() == t.len());
    if s.len() == 0 {
        assert(t == s);
    } else {
        assert(t[i as int] == s[j as int] && t[j as int] == s[i as int]);
        assert(forall|k: int| 0 <= k < s.len() && k != i && k != j ==> t[k] == s[k]);
    }
    
    0
}

}