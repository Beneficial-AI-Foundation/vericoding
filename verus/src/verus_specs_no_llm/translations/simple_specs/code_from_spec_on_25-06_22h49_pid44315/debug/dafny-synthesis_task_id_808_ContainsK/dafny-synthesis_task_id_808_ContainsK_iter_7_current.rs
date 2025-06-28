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
        // If k were in s, then by definition of membership in sequences,
        // there would exist some index j where 0 <= j < s.len() and s[j] == k
        // But our invariant states that for all j where 0 <= j < s.len(), s[j] != k
        // This is a direct contradiction
        if k in s {
            // k in s means there exists some valid index where s contains k
            // But we've proven that no such index exists
            // The contradiction is immediate from the definition of sequence membership
            // and our proven invariant
        }
    };
    
    return false;
}

}