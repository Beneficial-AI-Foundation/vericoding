use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn StringSwap(s: String, i: nat, j: nat) -> (t: String)
    requires 
        s.len() > 0 ==> i < s.len() && j < s.len()
    ensures 
        s.len() == t.len(),
        s.len() == 0 ==> t == s,
        s.len() > 0 ==> t@[i as int] == s@[j as int] && t@[j as int] == s@[i as int],
        s.len() > 0 ==> forall|k: int| 0 <= k < s.len() && k != i && k != j ==> t@[k] == s@[k]
{
    if s.len() == 0 {
        s
    } else {
        // Get the characters to swap
        let char_i = s@[i as int];
        let char_j = s@[j as int];
        
        // Create new string by building character by character
        let mut result = String::new();
        let mut idx = 0;
        
        while idx < s.len()
            invariant
                idx <= s.len(),
                result.len() == idx,
                forall|k: int| 0 <= k < idx ==> {
                    if k == i {
                        result@[k] == char_j
                    } else if k == j {
                        result@[k] == char_i
                    } else {
                        result@[k] == s@[k]
                    }
                }
        {
            if idx == i {
                result.push(char_j);
            } else if idx == j {
                result.push(char_i);
            } else {
                result.push(s@[idx as int]);
            }
            idx += 1;
        }
        
        // Final assertions to help verification
        assert(result.len() == s.len());
        assert(result@[i as int] == s@[j as int]);
        assert(result@[j as int] == s@[i as int]);
        assert(forall|k: int| 0 <= k < s.len() && k != i && k != j ==> result@[k] == s@[k]);
        
        result
    }
}

method check(s: String, i: nat, j: nat) -> (result: int)
    requires
        s.len() > 0 ==> i < s.len() && j < s.len()
{
    let t = StringSwap(s, i, j);
    
    assert(s.len() == t.len());
    if s.len() == 0 {
        assert(t == s);
    } else {
        assert(t@[i as int] == s@[j as int] && t@[j as int] == s@[i as int]);
        assert(forall|k: int| 0 <= k < s.len() && k != i && k != j ==> t@[k] == s@[k]);
    }
    
    0
}

}