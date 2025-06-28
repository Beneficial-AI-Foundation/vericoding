use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn StringSwap(s: Seq<char>, i: nat, j: nat) -> (t: Seq<char>)
    requires 
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
        // Get the characters to swap
        let char_i = s[i as int];
        let char_j = s[j as int];
        
        // Create new sequence by mapping each position
        let result = Seq::new(s.len(), |k: int| {
            if k == i {
                char_j
            } else if k == j {
                char_i
            } else {
                s[k]
            }
        });
        
        // Help verification with assertions
        assert(result.len() == s.len());
        assert(result[i as int] == s[j as int]);
        assert(result[j as int] == s[i as int]);
        assert(forall|k: int| 0 <= k < s.len() && k != i && k != j ==> result[k] == s[k]);
        
        result
    }
}

method check(s: Seq<char>, i: nat, j: nat) -> (result: int)
    requires
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