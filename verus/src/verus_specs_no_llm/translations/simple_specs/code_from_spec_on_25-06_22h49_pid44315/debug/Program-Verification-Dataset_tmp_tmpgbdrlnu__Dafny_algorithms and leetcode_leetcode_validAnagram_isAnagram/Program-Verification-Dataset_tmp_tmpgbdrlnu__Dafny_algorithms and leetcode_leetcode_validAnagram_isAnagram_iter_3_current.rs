use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper spec function to convert a string to a multiset
spec fn string_to_multiset(s: &str) -> Multiset<char> {
    s@.to_multiset()
}

fn toMultiset(s: &str) -> (mset: Multiset<char>)
    ensures mset == string_to_multiset(s)
{
    let mut result = Multiset::empty();
    let mut i = 0;
    
    while i < s.len()
        invariant 
            0 <= i <= s.len(),
            result == s@.subrange(0, i as int).to_multiset()
    {
        let c = s.as_bytes()[i] as char;
        result = result.add(c);
        i += 1;
    }
    
    assert(s@.subrange(0, s.len() as int) == s@);
    result
}

fn msetEqual(s: Multiset<char>, t: Multiset<char>) -> (equal: bool)
    ensures equal <==> (s == t)
{
    s =~= t
}

fn isAnagram(s: &str, t: &str) -> (equal: bool)
    ensures equal <==> (string_to_multiset(s) == string_to_multiset(t))
{
    let s_mset = toMultiset(s);
    let t_mset = toMultiset(t);
    msetEqual(s_mset, t_mset)
}

}