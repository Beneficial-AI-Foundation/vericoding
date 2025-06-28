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

// Simpler lemma that directly relates total and indexing
proof fn total_step_lemma(s: Seq<nat>, i: nat)
    requires
        i < s.len(),
    ensures
        total(s.subrange(0, (i + 1) as int)) == total(s.subrange(0, i as int)) + s[i as int],
{
    if i == 0 {
        // Base case: subrange(0, 1) vs subrange(0, 0)
        assert(s.subrange(0, 0) =~= seq![]);
        assert(s.subrange(0, 1) =~= seq![s[0]]);
        assert(total(s.subrange(0, 0)) == 0);
        assert(total(s.subrange(0, 1)) == s[0] + total(seq![]) == s[0]);
    } else {
        // Recursive case
        let prev = s.subrange(0, i as int);
        let curr = s.subrange(0, (i + 1) as int);
        
        // Key insight: curr = prev + [s[i]]
        assert(curr.len() == prev.len() + 1);
        assert(curr.first() == prev.first());
        assert(curr.drop_first() =~= prev.drop_first().push(s[i as int]));
        
        // Use the recursive definition
        total_step_lemma(s, i - 1);
        
        // Apply total definition
        assert(total(curr) == curr.first() + total(curr.drop_first()));
        assert(total(prev) == prev.first() + total(prev.drop_first()));
        
        // The relationship holds
        assert(total(curr.drop_first()) == total(prev.drop_first()) + s[i as int]);
        assert(total(curr) == total(prev) + s[i as int]);
    }
}

// Alternative simpler approach using mathematical properties
proof fn total_extends(s: Seq<nat>, i: usize)
    requires
        i < s.len(),
    ensures
        total(s.subrange(0, (i + 1) as int)) == total(s.subrange(0, i as int)) + s[i as int],
{
    let sub_i = s.subrange(0, i as int);
    let sub_i_plus_1 = s.subrange(0, (i + 1) as int);
    
    if i == 0 {
        assert(sub_i =~= seq![]);
        assert(sub_i_plus_1 =~= seq![s[0]]);
        assert(total(sub_i) == 0);
        assert(total(sub_i_plus_1) == s[0]);
    } else {
        // Use structural induction
        assert(sub_i_plus_1.first() == sub_i.first());
        assert(sub_i_plus_1.drop_first() =~= sub_i.drop_first().push(s[i as int]));
        
        // Apply the inductive step
        total_extends(s, i - 1);
        
        // total is additive over concatenation
        total_push_lemma(sub_i.drop_first(), s[i as int]);
        
        assert(total(sub_i_plus_1) == sub_i_plus_1.first() + total(sub_i_plus_1.drop_first()));
        assert(total(sub_i_plus_1) == sub_i.first() + total(sub_i.drop_first()) + s[i as int]);
        assert(total(sub_i_plus_1) == total(sub_i) + s[i as int]);
    }
}

// Helper lemma for pushing an element
proof fn total_push_lemma(s: Seq<nat>, x: nat)
    ensures
        total(s.push(x)) == total(s) + x,
    decreases s.len()
{
    if s.len() == 0 {
        assert(s.push(x) =~= seq![x]);
        assert(total(s.push(x)) == x);
        assert(total(s) == 0);
    } else {
        assert(s.push(x).first() == s.first());
        assert(s.push(x).drop_first() =~= s.drop_first().push(x));
        total_push_lemma(s.drop_first(), x);
        assert(total(s.push(x)) == s.first() + total(s.drop_first().push(x)));
        assert(total(s.push(x)) == s.first() + total(s.drop_first()) + x);
        assert(total(s.push(x)) == total(s) + x);
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
            total_extends(a, i);
        }
        sum = sum + a[i];
        i = i + 1;
    }
    
    sum
}

}