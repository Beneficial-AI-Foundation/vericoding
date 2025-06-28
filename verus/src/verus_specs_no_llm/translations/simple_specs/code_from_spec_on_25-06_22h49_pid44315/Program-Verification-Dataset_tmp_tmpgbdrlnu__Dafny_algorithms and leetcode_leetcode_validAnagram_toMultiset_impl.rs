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
        seq_to_multiset(s.subrange(0, s.len() - 1)).insert(s[s.len() - 1])
    }
}

proof fn seq_to_multiset_subrange_lemma(s: Seq<char>, i: int)
    requires 0 <= i < s.len()
    ensures seq_to_multiset(s.subrange(0, i + 1)) == seq_to_multiset(s.subrange(0, i)).insert(s[i])
    decreases s.len() - i
{
    let sub_i = s.subrange(0, i);
    let sub_i_plus_1 = s.subrange(0, i + 1);
    
    // Key insight: sub_i_plus_1 has one more element than sub_i
    assert(sub_i_plus_1.len() == i + 1);
    assert(sub_i.len() == i);
    
    if i == 0 {
        // Base case: sub_i is empty, sub_i_plus_1 has one element
        assert(sub_i.len() == 0);
        assert(seq_to_multiset(sub_i) == Multiset::empty());
        assert(sub_i_plus_1.len() == 1);
        assert(sub_i_plus_1[0] == s[0]);
        // Apply definition of seq_to_multiset for length 1
        assert(seq_to_multiset(sub_i_plus_1) == seq_to_multiset(sub_i_plus_1.subrange(0, 0)).insert(sub_i_plus_1[0]));
        assert(sub_i_plus_1.subrange(0, 0) == Seq::empty());
        assert(seq_to_multiset(sub_i_plus_1) == Multiset::empty().insert(s[0]));
        assert(seq_to_multiset(sub_i_plus_1) == seq_to_multiset(sub_i).insert(s[0]));
    } else {
        // Inductive case: use the definition of seq_to_multiset
        assert(sub_i_plus_1.len() > 0);
        assert(sub_i_plus_1[sub_i_plus_1.len() - 1] == s[i]);
        assert(sub_i_plus_1.subrange(0, sub_i_plus_1.len() - 1) == sub_i);
        
        // Apply the definition of seq_to_multiset
        assert(seq_to_multiset(sub_i_plus_1) == seq_to_multiset(sub_i_plus_1.subrange(0, sub_i_plus_1.len() - 1)).insert(sub_i_plus_1[sub_i_plus_1.len() - 1]));
        assert(seq_to_multiset(sub_i_plus_1) == seq_to_multiset(sub_i).insert(s[i]));
    }
}

proof fn seq_to_multiset_full_seq_lemma(s: Seq<char>)
    ensures s.subrange(0, s.len() as int) == s
{
    // This is a basic property of subrange
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
        // Before the update, establish the relationship for the next iteration
        proof {
            seq_to_multiset_subrange_lemma(s, i as int);
        }
        
        result = result.insert(s[i]);
        i = i + 1;
    }
    
    proof {
        seq_to_multiset_full_seq_lemma(s);
        assert(i == s.len());
        assert(result == seq_to_multiset(s.subrange(0, s.len() as int)));
        assert(s.subrange(0, s.len() as int) == s);
    }
    
    result
}

}