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

// Lemma to show relationship between subranges
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
        // Show that sub_i_plus_1 = sub_i.push(s[i])
        assert(sub_i_plus_1.len() == sub_i.len() + 1);
        assert(forall|j: int| 0 <= j < sub_i.len() ==> sub_i_plus_1[j] == sub_i[j]);
        assert(sub_i_plus_1[sub_i.len()] == s[i as int]);
        assert(sub_i_plus_1 =~= sub_i.push(s[i as int]));
        
        // Use the push lemma
        total_push_lemma(sub_i, s[i as int]);
        assert(total(sub_i_plus_1) == total(sub_i) + s[i as int]);
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