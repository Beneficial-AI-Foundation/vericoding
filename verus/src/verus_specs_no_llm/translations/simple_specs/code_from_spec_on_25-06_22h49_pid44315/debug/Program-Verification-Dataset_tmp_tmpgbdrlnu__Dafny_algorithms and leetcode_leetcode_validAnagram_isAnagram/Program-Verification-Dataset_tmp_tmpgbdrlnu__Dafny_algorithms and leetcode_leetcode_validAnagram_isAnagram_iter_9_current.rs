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

fn toMultiset(s: &str) -> (mset: Map<char, nat>)
    ensures mset == string_to_multiset(s)
{
    let mut result: Map<char, nat> = Map::empty();
    let mut i: usize = 0;
    
    while i < s.len()
        invariant 
            0 <= i <= s.len(),
            result == string_to_multiset_rec(s@, i as int, Map::empty())
    {
        let c = s@.index(i as int);
        let new_count = if result.contains_key(c) { result[c] + 1 } else { 1 };
        result = result.insert(c, new_count);
        i += 1;
    }
    
    assert(i == s.len());
    assert(result == string_to_multiset_rec(s@, i as int, Map::empty()));
    assert(result == string_to_multiset_rec(s@, s@.len(), Map::empty()));
    assert(result == string_to_multiset(s));
    
    result
}

// Helper spec function to check if two maps are equal
spec fn maps_equal(s: Map<char, nat>, t: Map<char, nat>) -> bool {
    s.dom() == t.dom() && 
    forall |k: char| s.dom().contains(k) ==> s[k] == t[k]
}

// Lemma to prove that maps_equal is equivalent to structural equality
proof fn lemma_maps_equal_equiv(s: Map<char, nat>, t: Map<char, nat>)
    ensures maps_equal(s, t) <==> (s == t)
{
    if maps_equal(s, t) {
        assert(s.dom() == t.dom());
        assert(forall |k: char| s.dom().contains(k) ==> s[k] == t[k]);
        assert(s =~= t);
    }
    if s == t {
        assert(s.dom() == t.dom());
        assert(forall |k: char| s.dom().contains(k) ==> s[k] == t[k]);
    }
}

fn msetEqual(s: Map<char, nat>, t: Map<char, nat>) -> (equal: bool)
    ensures equal <==> (s == t)
{
    proof {
        lemma_maps_equal_equiv(s, t);
    }
    
    // Check if domains are equal first
    if s.dom() != t.dom() {
        return false;
    }
    
    // Check if all values are equal
    let dom = s.dom();
    let dom_seq = dom.to_seq();
    let mut j = 0;
    
    while j < dom_seq.len()
        invariant
            0 <= j <= dom_seq.len(),
            forall |i: int| 0 <= i < j ==> s[dom_seq[i]] == t[dom_seq[i]]
    {
        let key = dom_seq[j as int];
        if s[key] != t[key] {
            return false;
        }
        j += 1;
    }
    
    assert(forall |k: char| s.dom().contains(k) ==> s[k] == t[k]);
    assert(maps_equal(s, t));
    
    true
}

fn isAnagram(s: &str, t: &str) -> (equal: bool)
    ensures equal <==> (string_to_multiset(s) == string_to_multiset(t))
{
    let s_mset = toMultiset(s);
    let t_mset = toMultiset(t);
    msetEqual(s_mset, t_mset)
}

}