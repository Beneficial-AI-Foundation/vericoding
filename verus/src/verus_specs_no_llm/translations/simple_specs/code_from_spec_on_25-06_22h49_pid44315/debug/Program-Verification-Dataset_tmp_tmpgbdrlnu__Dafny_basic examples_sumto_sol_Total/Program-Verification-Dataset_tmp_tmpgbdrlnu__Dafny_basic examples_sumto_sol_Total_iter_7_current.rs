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
        // The key insight: we can use the recursive structure of total
        let sub_i = s.subrange(0, i);
        let sub_i_plus_1 = s.subrange(0, i + 1);
        
        // Both have the same first element
        assert(sub_i.first() == s[0]);
        assert(sub_i_plus_1.first() == s[0]);
        
        // The tails are related
        let tail_i = sub_i.drop_first(); // s.subrange(1, i)
        let tail_i_plus_1 = sub_i_plus_1.drop_first(); // s.subrange(1, i+1)
        
        assert(tail_i =~= s.subrange(1, i));
        assert(tail_i_plus_1 =~= s.subrange(1, i + 1));
        
        // Apply induction on the tail
        if i > 1 {
            let shifted = s.subrange(1, s.len() as int);
            total_append_lemma(shifted, i - 1);
        } else {
            // i == 1: handle base case for tail
            assert(tail_i_plus_1 =~= seq![s[1]]);
            assert(tail_i =~= seq![]);
            assert(total(tail_i_plus_1) == s[1]);
            assert(total(tail_i) == 0);
        }
        
        // Now we can conclude
        assert(total(tail_i_plus_1) == total(tail_i) + s[i]);
        assert(total(sub_i_plus_1) == s[0] + total(tail_i_plus_1));
        assert(total(sub_i) == s[0] + total(tail_i));
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
            if i < a.len() {
                total_append_lemma(a, i as int);
            }
        }
        sum = sum + a[i];
        i = i + 1;
    }
    
    sum
}

}