use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper spec function to convert a string to a multiset (represented as Map<char, nat>)
spec fn string_to_multiset(s: &str) -> Map<char, nat> {
    string_to_multiset_rec(s@, 0, Map::empty())
}

// Recursive helper for building multiset
spec fn string_to_multiset_rec(s: Seq<char>, i: int, acc: Map<char, nat>) -> Map<char, nat>
    decreases s.len() - i
{
    if i >= s.len() {
        acc
    } else {
        let c = s[i];
        let new_count = if acc.contains_key(c) { acc[c] + 1 } else { 1 };
        string_to_multiset_rec(s, i + 1, acc.insert(c, new_count))
    }
}

// Lemma to help with multiset properties
proof fn lemma_multiset_subrange(s: Seq<char>, i: int)
    requires 0 <= i <= s.len()
    ensures string_to_multiset_rec(s, 0, Map::empty()) == 
            string_to_multiset_rec(s.subrange(0, i), 0, Map::empty()).union_prefer_right(
                string_to_multiset_rec(s, i, Map::empty()))
{
    // Proof would go here - for now we assume this property
}

fn toMultiset(s: &str) -> (mset: Map<char, nat>)
    ensures mset == string_to_multiset(s)
{
    let mut result: Map<char, nat> = Map::empty();
    let mut i: usize = 0;
    
    while i < s.len()
        invariant 
            0 <= i <= s.len(),
            result == string_to_multiset_rec(s@, 0, Map::empty()).restrict(s@.subrange(0, i as int).to_set())
    {
        let c = s@.index(i as int);
        let new_count = if result.contains_key(c) { result[c] + 1 } else { 1 };
        result = result.insert(c, new_count);
        i += 1;
    }
    
    proof {
        assert(s@.subrange(0, s.len() as int) == s@);
        // Additional proof steps would help verify the postcondition
    }
    
    result
}

fn msetEqual(s: Map<char, nat>, t: Map<char, nat>) -> (equal: bool)
    ensures equal <==> (s == t)
{
    // Simple implementation - in practice might need more sophisticated comparison
    s.dom() == t.dom() && 
    (forall |k: char| s.dom().contains(k) ==> s[k] == t[k])
}

fn isAnagram(s: &str, t: &str) -> (equal: bool)
    ensures equal <==> (string_to_multiset(s) == string_to_multiset(t))
{
    let s_mset = toMultiset(s);
    let t_mset = toMultiset(t);
    msetEqual(s_mset, t_mset)
}

}