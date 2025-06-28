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

// Helper spec function for the invariant
spec fn string_to_multiset_from(s: Seq<char>, start: int) -> Map<char, nat> {
    string_to_multiset_rec(s, start, Map::empty())
}

fn toMultiset(s: &str) -> (mset: Map<char, nat>)
    ensures mset == string_to_multiset(s)
{
    let mut result: Map<char, nat> = Map::empty();
    let mut i: usize = 0;
    
    while i < s.len()
        invariant 
            0 <= i <= s.len(),
            result == string_to_multiset_rec(s@, 0, string_to_multiset_rec(s@, i as int, Map::empty()))
    {
        let c = s@.index(i as int);
        let new_count = if result.contains_key(c) { result[c] + 1 } else { 1 };
        result = result.insert(c, new_count);
        i += 1;
    }
    
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
        assert(s.ext_equal(t));
    }
    if s == t {
        assert(s.dom() == t.dom());
        assert(forall |k: char| s.dom().contains(k) ==> s[k] == t[k]);
    }
}

// Helper function to check finite set membership iteratively
fn check_all_keys_equal(s: Map<char, nat>, t: Map<char, nat>, keys: Set<char>) -> (result: bool)
    requires s.dom() == keys && t.dom() == keys
    ensures result <==> (forall |k: char| keys.contains(k) ==> s[k] == t[k])
{
    if keys.is_empty() {
        return true;
    }
    
    let key = keys.choose();
    if s[key] != t[key] {
        return false;
    }
    
    let remaining_keys = keys.remove(key);
    check_all_keys_equal(s.remove(key), t.remove(key), remaining_keys)
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
    
    // Check if all values are equal for keys in the domain
    let result = check_all_keys_equal(s, t, s.dom());
    
    assert(result <==> (forall |k: char| s.dom().contains(k) ==> s[k] == t[k]));
    assert(result <==> maps_equal(s, t));
    
    result
}

fn isAnagram(s: &str, t: &str) -> (equal: bool)
    ensures equal <==> (string_to_multiset(s) == string_to_multiset(t))
{
    let s_mset = toMultiset(s);
    let t_mset = toMultiset(t);
    msetEqual(s_mset, t_mset)
}

}