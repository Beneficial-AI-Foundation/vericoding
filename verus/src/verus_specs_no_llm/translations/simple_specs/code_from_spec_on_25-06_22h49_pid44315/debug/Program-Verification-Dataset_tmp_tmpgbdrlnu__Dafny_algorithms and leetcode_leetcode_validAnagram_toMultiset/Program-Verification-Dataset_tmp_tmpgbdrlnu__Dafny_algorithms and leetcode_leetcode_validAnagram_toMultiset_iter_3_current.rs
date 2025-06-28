use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn toMultiset(s: Seq<char>) -> (mset: Multiset<char>)
    ensures
        s.to_multiset() == mset
{
    seq_to_multiset(s)
}

spec fn seq_to_multiset<T>(s: Seq<T>) -> Multiset<T>
    decreases s.len()
{
    if s.len() == 0 {
        Multiset::empty()
    } else {
        seq_to_multiset(s.drop_last()).insert(s.last())
    }
}

proof fn seq_to_multiset_correct<T>(s: Seq<T>)
    ensures seq_to_multiset(s) == s.to_multiset()
    decreases s.len()
{
    if s.len() == 0 {
        assert(seq_to_multiset(s) == Multiset::empty());
        assert(s.to_multiset() == Multiset::empty());
    } else {
        seq_to_multiset_correct(s.drop_last());
        assert(seq_to_multiset(s) == seq_to_multiset(s.drop_last()).insert(s.last()));
        assert(s.to_multiset() == s.drop_last().to_multiset().insert(s.last()));
    }
}

}