use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn msetEqual(s: Multiset<char>, t: Multiset<char>) -> (equal: bool)
    ensures
        s == t <==> equal
{
    s == t
}

}