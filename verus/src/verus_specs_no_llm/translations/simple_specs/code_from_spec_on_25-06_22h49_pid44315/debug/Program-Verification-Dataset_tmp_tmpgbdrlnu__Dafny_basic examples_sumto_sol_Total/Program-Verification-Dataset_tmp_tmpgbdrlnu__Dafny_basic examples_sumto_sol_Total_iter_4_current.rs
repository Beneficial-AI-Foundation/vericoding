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
{
    if i == 0 {
        assert(s.subrange(0, 1) =~= seq![s[0]]);
        assert(s.subrange(0, 0) =~= seq![]);
        assert(total(seq![s[0]]) == s[0] + total(seq![]));
        assert(total(seq![]) == 0);
    } else {
        total_append_lemma(s, i - 1);
        
        // Key insight: relate the structure of subranges
        let sub_i_plus_1 = s.subrange(0, i + 1);
        let sub_i = s.subrange(0, i);
        
        assert(sub_i_plus_1.len() == i + 1);
        assert(sub_i.len() == i);
        assert(sub_i_plus_1.first() == s[0]);
        assert(sub_i.first() == s[0]);
        assert(sub_i_plus_1.drop_first() =~= s.subrange(1, i + 1));
        assert(sub_i.drop_first() =~= s.subrange(1, i));
        
        // Recursively apply the same reasoning to the tail
        if i > 1 {
            total_append_lemma(s.subrange(1, s.len()), i - 1);
        }
        
        // The key relationship
        assert(total(s.subrange(1, i + 1)) == total(s.subrange(1, i)) + s[i]);
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