use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ContainsK(s: Seq<int>, k: int) -> (result: bool)
    ensures
        result <==> k in s
{
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|j: int| 0 <= j < i ==> s[j] != k,
    {
        if s[i] == k {
            return true;
        }
        i = i + 1;
    }
    
    // Prove that k is not in s when we exit the loop
    assert forall|j: int| 0 <= j < s.len() implies s[j] != k by {
        // When we exit the loop, i == s.len()
        // Our invariant tells us that for all j where 0 <= j < i, s[j] != k
        // Since i == s.len(), this covers all valid indices in the sequence
    };
    
    return false;
}

}