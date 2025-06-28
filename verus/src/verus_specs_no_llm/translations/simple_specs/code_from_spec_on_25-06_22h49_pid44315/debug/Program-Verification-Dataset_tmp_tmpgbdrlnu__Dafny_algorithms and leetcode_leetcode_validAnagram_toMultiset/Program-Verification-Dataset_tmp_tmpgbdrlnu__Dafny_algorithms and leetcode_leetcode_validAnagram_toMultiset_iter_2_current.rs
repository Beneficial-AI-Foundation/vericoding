use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn toMultiset(s: Seq<char>) -> (mset: Multiset<char>)
    ensures
        s.to_multiset() == mset
{
    s.to_multiset()
}

}