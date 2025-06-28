use builtin::*;
use builtin_macros::*;

verus! {

use vstd::multiset::Multiset;

fn main() {
}

fn msetEqual(s: Multiset<char>, t: Multiset<char>) -> (equal: bool)
    ensures
        equal <==> (s == t)
{
    s == t
}

}