use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn toMultiset(s: &str) -> (mset: Multiset<char>)
    ensures mset == s.to_multiset()
{
    s.to_multiset()
}

fn msetEqual(s: Multiset<char>, t: Multiset<char>) -> (equal: bool)
    ensures equal <==> (s == t)
{
    s == t
}

fn isAnagram(s: &str, t: &str) -> (equal: bool)
    ensures equal <==> (s.to_multiset() == t.to_multiset())
{
    let s_mset = s.to_multiset();
    let t_mset = t.to_multiset();
    s_mset == t_mset
}

}