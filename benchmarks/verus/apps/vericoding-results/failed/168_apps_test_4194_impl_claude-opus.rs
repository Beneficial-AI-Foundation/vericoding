// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, m: int, a: Seq<int>) -> bool {
    n >= 0 && m >= 0 && m == a.len()
}

spec fn can_complete_all_assignments(n: int, a: Seq<int>) -> bool {
    sum_seq(a) <= n
}

spec fn total_assignment_days(a: Seq<int>) -> int {
    sum_seq(a)
}

spec fn sum_seq(s: Seq<int>) -> int 
    decreases s.len()
{
    if s.len() == 0 { 
        0 
    } else { 
        s[0] + sum_seq(s.subrange(1, s.len() as int))
    }
}
// </vc-preamble>

// <vc-helpers>
proof fn sum_seq_empty()
    ensures sum_seq(Seq::<int>::empty()) == 0
{
}

/* helper modified by LLM (iteration 4): fixed type mismatch in sum_seq_push lemma */
proof fn sum_seq_push(s: Seq<int>, x: int)
    ensures sum_seq(s.push(x)) == sum_seq(s) + x
    decreases s.len()
{
    if s.len() == 0 {
        // Base case: empty sequence
        assert(s =~= Seq::<int>::empty());
        assert(s.push(x).len() == 1);
        assert(s.push(x)[0] == x);
        assert(s.push(x).subrange(1, 1) =~= Seq::<int>::empty());
        assert(sum_seq(s.push(x)) == s.push(x)[0] + sum_seq(s.push(x).subrange(1, 1)));
        assert(sum_seq(s.push(x)) == x + sum_seq(Seq::<int>::empty()));
        assert(sum_seq(s.push(x)) == x + 0);
        assert(sum_seq(s) == 0);
    } else {
        // Recursive case
        let s_push = s.push(x);
        assert(s_push.len() == s.len() + 1);
        assert(s_push[0] == s[0]);
        
        // Key insight: when we push x to s, the subrange from 1 to end is s.subrange(1, s.len()).push(x)
        assert(forall|i: int| 1 <= i < s.len() ==> s_push[i] == s[i]);
        assert(s_push[s.len() as int] == x);
        
        let tail = s.subrange(1, s.len() as int);
        let tail_push = tail.push(x);
        
        assert(s_push.subrange(1, s_push.len() as int) =~= tail_push);
        
        // Apply induction hypothesis
        sum_seq_push(tail, x);
        
        // Now prove the main equality
        assert(sum_seq(s_push) == s_push[0] + sum_seq(s_push.subrange(1, s_push.len() as int)));
        assert(sum_seq(s_push) == s[0] + sum_seq(tail_push));
        assert(sum_seq(s_push) == s[0] + (sum_seq(tail) + x));
        assert(sum_seq(s) == s[0] + sum_seq(tail));
        assert(sum_seq(s_push) == sum_seq(s) + x);
    }
}

proof fn sum_vec_relation(v: Vec<i8>, i: int)
    requires
        0 <= i <= v.len(),
    ensures
        sum_seq(v@.subrange(0, i).map(|j, x: i8| x as int)) == sum_seq(v@.map(|j, x: i8| x as int).subrange(0, i))
    decreases i
{
    if i == 0 {
        assert(v@.subrange(0, 0) =~= Seq::<i8>::empty());
        assert(v@.subrange(0, 0).map(|j, x: i8| x as int) =~= Seq::<int>::empty());
        assert(v@.map(|j, x: i8| x as int).subrange(0, 0) =~= Seq::<int>::empty());
    } else {
        sum_vec_relation(v, i - 1);
        assert(v@.subrange(0, i) =~= v@.subrange(0, i - 1).push(v@[i - 1]));
        assert(v@.subrange(0, i).map(|j, x: i8| x as int) =~= v@.subrange(0, i - 1).map(|j, x: i8| x as int).push(v@[i - 1] as int));
        sum_seq_push(v@.subrange(0, i - 1).map(|j, x: i8| x as int), v@[i - 1] as int);
        assert(v@.map(|j, x: i8| x as int).subrange(0, i) =~= v@.map(|j, x: i8| x as int).subrange(0, i - 1).push(v@.map(|j, x: i8| x as int)[i - 1]));
        assert(v@.map(|j, x: i8| x as int)[i - 1] == v@[i - 1] as int);
        sum_seq_push(v@.map(|j, x: i8| x as int).subrange(0, i - 1), v@[i - 1] as int);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, a: Vec<i8>) -> (result: i8)
    requires 
        valid_input(n as int, m as int, a@.map(|i, x: i8| x as int))
    ensures 
        m as int == 0 ==> result as int == n as int,
        m as int > 0 && can_complete_all_assignments(n as int, a@.map(|i, x: i8| x as int)) ==> result as int == n as int - total_assignment_days(a@.map(|i, x: i8| x as int)),
        m as int > 0 && !can_complete_all_assignments(n as int, a@.map(|i, x: i8| x as int)) ==> result as int == -1,
        result as int >= -1
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): fixed overflow check and return logic for m == 0 case */
    if m == 0 {
        proof {
            assert(a@.len() == 0);
            assert(a@.map(|i, x: i8| x as int) =~= Seq::<int>::empty());
            assert(sum_seq(a@.map(|i, x: i8| x as int)) == 0);
            assert(can_complete_all_assignments(n as int, a@.map(|i, x: i8| x as int)));
        }
        return n;
    }
    
    let mut sum: i8 = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            sum as int == sum_seq(a@.subrange(0, i as int).map(|j, x: i8| x as int)),
            sum >= 0,
            sum <= 127,
        decreases a.len() - i
    {
        // Check for overflow before adding
        if a[i] > 0 && sum > 127 - a[i] {
            // Would overflow, so total sum exceeds n
            proof {
                // The partial sum plus remaining elements would exceed 127
                // Since we can't complete without overflow, return -1
            }
            return -1;
        }
        
        sum = sum + a[i];
        
        proof {
            assert(a@.subrange(0, (i + 1) as int) =~= a@.subrange(0, i as int).push(a@[i as int]));
            assert(a@.subrange(0, (i + 1) as int).map(|j, x: i8| x as int) =~= a@.subrange(0, i as int).map(|j, x: i8| x as int).push(a@[i as int] as int));
            sum_seq_push(a@.subrange(0, i as int).map(|j, x: i8| x as int), a@[i as int] as int);
        }
        
        i = i + 1;
    }
    
    proof {
        assert(a@.subrange(0, a.len() as int) =~= a@);
        assert(sum as int == sum_seq(a@.map(|j, x: i8| x as int)));
    }
    
    if sum > n {
        -1
    } else {
        n - sum
    }
}
// </vc-code>


}

fn main() {}