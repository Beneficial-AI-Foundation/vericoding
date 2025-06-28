// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Partition(m: multiset<int>) -> (pre: multiset<int>, p: int, post: multiset<int>)
    requires
        m.len() > 0
    ensures
        p in m,
        m == pre+multiset
{
    return (0, 0, 0);
}

}