use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn msetEqual(s: multiset<char>, t: multiset<char>) -> (equal: bool)
    ensures
        s == t <==> equal
{
    s == t
}

}