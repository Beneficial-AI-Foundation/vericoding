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
        // Convert string to sequence of characters for manipulation
        let s_seq = s@;
        
        // Create new sequence with swapped characters
        let t_seq = s_seq.update(i as int, s_seq[j as int]).update(j as int, s_seq[i as int]);
        
        // Convert back to string
        let t = String::from_seq(t_seq);
        
        // Proof assertions to help verification
        assert(t.len() == s.len());
        assert(t[i as int] == s[j as int]);
        assert(t[j as int] == s[i as int]);
        
        // Prove that other characters remain unchanged
        assert(forall|k: int| 0 <= k < s.len() && k != i && k != j ==> {
            t[k] == s[k]
        }) by {
            assert(forall|k: int| 0 <= k < s.len() && k != i && k != j ==> {
                t_seq[k] == s_seq[k]
            });
        }
        
        t
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