use builtin::*;
use builtin_macros::*;

verus! {

use vstd::multiset::*;

fn main() {
}

fn msetEqual(s: Multiset<char>, t: Multiset<char>) -> (equal: bool)
    ensures
        equal <==> (s == t)
{
    // The implementation directly compares the multisets
    // This should verify since we're returning exactly what the postcondition expects
    s == t
}

}