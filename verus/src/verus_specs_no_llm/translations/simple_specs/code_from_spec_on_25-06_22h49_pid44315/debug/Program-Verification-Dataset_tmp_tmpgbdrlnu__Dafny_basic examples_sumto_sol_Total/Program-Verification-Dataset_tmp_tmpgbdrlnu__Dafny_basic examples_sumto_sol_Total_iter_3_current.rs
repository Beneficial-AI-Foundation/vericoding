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
    } else {
        total_append_lemma(s, i - 1);
        assert(s.subrange(0, i + 1).drop_first() =~= s.subrange(1, i + 1));
        assert(s.subrange(0, i).drop_first() =~= s.subrange(1, i));
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