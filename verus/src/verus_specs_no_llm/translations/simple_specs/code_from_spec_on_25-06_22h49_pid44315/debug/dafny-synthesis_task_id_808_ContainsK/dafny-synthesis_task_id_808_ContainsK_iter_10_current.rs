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
    
    // When we exit the loop, i == s.len()
    // Our invariant tells us that forall j: 0 <= j < i ==> s[j] != k
    // Since i == s.len(), we have forall j: 0 <= j < s.len() ==> s[j] != k
    assert(forall|j: int| 0 <= j < s.len() ==> s[j] != k);
    
    // This means k is not in s
    // We can prove this directly from the invariant
    assert(!(k in s));
    
    return false;
}

}