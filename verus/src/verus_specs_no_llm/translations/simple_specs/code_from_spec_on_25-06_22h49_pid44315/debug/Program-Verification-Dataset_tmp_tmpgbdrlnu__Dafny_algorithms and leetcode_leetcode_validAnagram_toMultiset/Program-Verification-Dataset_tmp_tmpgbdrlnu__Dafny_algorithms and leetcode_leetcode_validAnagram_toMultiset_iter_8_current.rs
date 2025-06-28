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

proof fn seq_to_multiset_subrange_lemma(s: Seq<char>, i: int)
    requires 0 <= i < s.len()
    ensures seq_to_multiset(s.subrange(0, i + 1)) == seq_to_multiset(s.subrange(0, i)).insert(s[i])
    decreases s.len() - i
{
    let sub_i = s.subrange(0, i);
    let sub_i_plus_1 = s.subrange(0, i + 1);
    
    assert(sub_i_plus_1.len() == i + 1);
    assert(sub_i_plus_1.last() == s[i]);
    assert(sub_i_plus_1.drop_last() =~= sub_i);
    
    if i == 0 {
        assert(sub_i.len() == 0);
        assert(seq_to_multiset(sub_i) == Multiset::empty());
        assert(sub_i_plus_1.len() == 1);
        assert(seq_to_multiset(sub_i_plus_1) == Multiset::empty().insert(sub_i_plus_1.last()));
        assert(sub_i_plus_1.last() == s[0]);
    } else {
        assert(sub_i_plus_1.len() > 0);
        assert(seq_to_multiset(sub_i_plus_1) == seq_to_multiset(sub_i_plus_1.drop_last()).insert(sub_i_plus_1.last()));
        assert(sub_i_plus_1.drop_last() =~= sub_i);
        assert(sub_i_plus_1.last() == s[i]);
    }
}

proof fn seq_to_multiset_full_seq_lemma(s: Seq<char>)
    ensures s.subrange(0, s.len() as int) =~= s
{
    assert(s.subrange(0, s.len() as int) =~= s);
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
        proof {
            if i < s.len() {
                seq_to_multiset_subrange_lemma(s, i as int);
                assert(seq_to_multiset(s.subrange(0, (i + 1) as int)) == 
                       seq_to_multiset(s.subrange(0, i as int)).insert(s[i as int]));
                assert(seq_to_multiset(s.subrange(0, i as int)) == result);
            }
        }
        result = result.insert(s[i]);
        i = i + 1;
        proof {
            assert(result == seq_to_multiset(s.subrange(0, i as int)));
        }
    }
    
    proof {
        seq_to_multiset_full_seq_lemma(s);
        assert(i == s.len());
        assert(result == seq_to_multiset(s.subrange(0, s.len() as int)));
        assert(s.subrange(0, s.len() as int) =~= s);
        assert(seq_to_multiset(s.subrange(0, s.len() as int)) == seq_to_multiset(s));
    }
    
    result
}

}