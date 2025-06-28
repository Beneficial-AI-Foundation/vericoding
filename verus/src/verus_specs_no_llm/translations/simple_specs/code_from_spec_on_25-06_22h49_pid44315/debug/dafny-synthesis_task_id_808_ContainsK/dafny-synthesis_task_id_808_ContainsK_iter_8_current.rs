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
            // We found k at position i, so k is in s
            assert(s[i as int] == k);
            assert(k in s);
            return true;
        }
        i = i + 1;
    }
    
    // When we exit the loop, i == s.len()
    // Our invariant tells us that forall j: 0 <= j < i ==> s[j] != k
    // Since i == s.len(), we have forall j: 0 <= j < s.len() ==> s[j] != k
    assert(i == s.len());
    assert(forall|j: int| 0 <= j < s.len() ==> s[j] != k);
    
    // This means k is not in s
    assert(!(k in s)) by {
        if k in s {
            // If k is in s, then there exists an index j such that s[j] == k
            // and 0 <= j < s.len() (by definition of sequence membership)
            // But our invariant says forall j: 0 <= j < s.len() ==> s[j] != k
            // This creates a direct contradiction
            assert(exists|j: int| 0 <= j < s.len() && s[j] == k);
            let j = choose|j: int| 0 <= j < s.len() && s[j] == k;
            assert(0 <= j < s.len() && s[j] == k);
            assert(s[j] != k); // from our proven invariant
            assert(false); // contradiction: s[j] == k and s[j] != k
        }
    };
    
    return false;
}

}