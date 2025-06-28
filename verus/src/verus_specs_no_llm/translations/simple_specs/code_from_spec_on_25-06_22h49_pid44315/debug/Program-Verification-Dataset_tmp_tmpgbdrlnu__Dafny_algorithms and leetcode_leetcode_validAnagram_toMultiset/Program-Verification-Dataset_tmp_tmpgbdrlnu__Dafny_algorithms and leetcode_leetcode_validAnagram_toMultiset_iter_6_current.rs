use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
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

fn toMultiset(s: Seq<char>) -> (mset: Multiset<char>)
    ensures
        seq_to_multiset(s) == mset
{
    let mut result = Multiset::empty();
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result == seq_to_multiset(s.subrange(0, i as int))
    {
        result = result.insert(s[i]);
        i = i + 1;
    }
    
    assert(s.subrange(0, s.len() as int) =~= s);
    result
}

}