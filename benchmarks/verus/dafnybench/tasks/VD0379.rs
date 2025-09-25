// <vc-preamble>
use vstd::prelude::*;
use vstd::multiset::*;

verus! {

proof fn to_multiset(s: &str) -> (mset: Multiset<char>)
    ensures mset == s@.to_multiset()
{
    assume(false);
    s@.to_multiset()
}

proof fn mset_equal(s: Multiset<char>, t: Multiset<char>) -> (equal: bool)
    ensures s == t <==> equal
{
    assume(false);
    true
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn is_anagram(s: &str, t: &str) -> (equal: bool)
    ensures (s@.to_multiset() == t@.to_multiset()) == equal
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}