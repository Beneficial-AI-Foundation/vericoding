use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn toMultiset(s: String) -> (mset: Multiset<char>)
    ensures mset == s.as_str().to_multiset()
{
    s.as_str().to_multiset()
}

method msetEqual(s: Multiset<char>, t: Multiset<char>) -> (equal: bool)
    ensures equal <==> (s == t)
{
    // In Verus, we can use the built-in equality for multisets
    s == t
}

method isAnagram(s: &str, t: &str) -> (equal: bool)
    ensures equal <==> (s.to_multiset() == t.to_multiset())
{
    let s_mset = s.to_multiset();
    let t_mset = t.to_multiset();
    s_mset == t_mset
}

}