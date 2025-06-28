use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Spec function to compute the total sum of a sequence
spec fn total(s: Seq<nat>) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        s.first() + total(s.drop_first())
    }
}

// Lemma to help with verification - proves that total of a range can be extended
proof fn total_append_lemma(s: Seq<nat>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        total(s.subrange(0, i + 1)) == total(s.subrange(0, i)) + s[i],
    decreases i
{
    if i == 0 {
        assert(s.subrange(0, 1) =~= seq![s[0]]);
        assert(s.subrange(0, 0) =~= seq![]);
        assert(total(s.subrange(0, 1)) == s[0] + total(seq![]));
        assert(total(s.subrange(0, 0)) == 0);
    } else {
        // Apply induction hypothesis
        total_append_lemma(s, i - 1);
        
        // Work with the structure of the sequences
        let sub_i_plus_1 = s.subrange(0, i + 1);
        let sub_i = s.subrange(0, i);
        
        // Both sequences have the same first element
        assert(sub_i_plus_1.first() == s[0]);
        assert(sub_i.first() == s[0]);
        
        // The relationship between their tails
        assert(sub_i_plus_1.drop_first() =~= s.subrange(1, i + 1));
        assert(sub_i.drop_first() =~= s.subrange(1, i));
        
        // Key insight: s.subrange(1, i+1) extends s.subrange(1, i) by one element
        if i > 1 {
            // We can apply our lemma to the shifted sequence s.subrange(1, s.len())
            let shifted_seq = s.subrange(1, s.len() as int);
            total_append_lemma(shifted_seq, i - 1);
            assert(total(shifted_seq.subrange(0, i)) == total(shifted_seq.subrange(0, i - 1)) + shifted_seq[i - 1]);
            // Note: shifted_seq.subrange(0, i) == s.subrange(1, i+1)
            // and shifted_seq.subrange(0, i-1) == s.subrange(1, i)
            // and shifted_seq[i-1] == s[i]
            assert(total(s.subrange(1, i + 1)) == total(s.subrange(1, i)) + s[i]);
        } else {
            // i == 1 case: handle directly
            assert(s.subrange(1, 2) =~= seq![s[1]]);
            assert(s.subrange(1, 1) =~= seq![]);
            assert(total(s.subrange(1, 2)) == s[1]);
            assert(total(s.subrange(1, 1)) == 0);
            assert(total(s.subrange(1, 2)) == total(s.subrange(1, 1)) + s[1]);
        }
        
        // Now conclude using the definition of total
        assert(total(sub_i_plus_1) == s[0] + total(s.subrange(1, i + 1)));
        assert(total(sub_i) == s[0] + total(s.subrange(1, i)));
        assert(total(sub_i_plus_1) == total(sub_i) + s[i]);
    }
}

fn Total(a: Seq<nat>) -> (r: nat)
    ensures
        r == total(a.subrange(0, a.len() as int))
{
    let mut sum: nat = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            sum == total(a.subrange(0, i as int))
    {
        proof {
            total_append_lemma(a, i as int);
        }
        sum = sum + a[i as int];
        i = i + 1;
    }
    
    sum
}

}