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
            result == string_to_multiset_rec(s@, 0, Map::empty())
    {
        let c = s@.index(i as int);
        let new_count = if result.contains_key(c) { result[c] + 1 } else { 1 };
        result = result.insert(c, new_count);
        i += 1;
    }
    
    result
}

fn msetEqual(s: Map<char, nat>, t: Map<char, nat>) -> (equal: bool)
    ensures equal <==> (s == t)
{
    if s.dom() != t.dom() {
        false
    } else {
        let mut keys = s.dom().to_seq();
        let mut i = 0;
        
        while i < keys.len()
            invariant
                0 <= i <= keys.len(),
                forall |j: int| 0 <= j < i ==> s[keys[j]] == t[keys[j]],
                s.dom() == t.dom()
        {
            if s[keys[i]] != t[keys[i]] {
                return false;
            }
            i += 1;
        }
        
        true
    }
}

fn isAnagram(s: &str, t: &str) -> (equal: bool)
    ensures equal <==> (string_to_multiset(s) == string_to_multiset(t))
{
    let s_mset = toMultiset(s);
    let t_mset = toMultiset(t);
    msetEqual(s_mset, t_mset)
}

}