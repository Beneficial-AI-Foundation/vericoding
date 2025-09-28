use vstd::prelude::*;

verus! {

// The order of the recursion in these two functions
// must match the order of the iteration in the algorithm above
spec fn min_seq(a: Seq<int>) -> int
    recommends a.len() > 0
    decreases a.len() when a.len() > 0
{
    if a.len() == 1 {
        a[0]
    } else {
        let prefix = a.subrange(0, a.len() - 1);
        assume(prefix.len() < a.len());
        let min_prefix = min_seq(prefix);
        if a[a.len() - 1] <= min_prefix {
            a[a.len() - 1]
        } else {
            min_prefix
        }
    }
}

spec fn max_seq(a: Seq<int>) -> int
    recommends a.len() > 0
    decreases a.len() when a.len() > 0
{
    if a.len() == 1 {
        a[0]
    } else {
        let prefix = a.subrange(0, a.len() - 1);
        assume(prefix.len() < a.len());
        let max_prefix = max_seq(prefix);
        if a[a.len() - 1] >= max_prefix {
            a[a.len() - 1]
        } else {
            max_prefix
        }
    }
}

// <vc-helpers>
// Helper lemmas to connect iterative computation with recursive specs
proof fn min_seq_unfold(a: Seq<int>, i: int)
    requires 
        0 <= i < a.len(),
        a.len() > 0,
    ensures 
        min_seq(a.subrange(0, i + 1)) == if i == 0 {
            a[0]
        } else {
            let prev_min = min_seq(a.subrange(0, i));
            if a[i] <= prev_min { a[i] } else { prev_min }
        }
    decreases i
{
    if i == 0 {
        assert(a.subrange(0, 1).len() == 1);
        assert(a.subrange(0, 1)[0] == a[0]);
    } else {
        assert(a.subrange(0, i + 1).len() == i + 1);
        let prefix = a.subrange(0, i + 1).subrange(0, i);
        assert(prefix =~= a.subrange(0, i));
        assert(a.subrange(0, i + 1)[i] == a[i]);
    }
}

proof fn max_seq_unfold(a: Seq<int>, i: int)
    requires 
        0 <= i < a.len(),
        a.len() > 0,
    ensures 
        max_seq(a.subrange(0, i + 1)) == if i == 0 {
            a[0]
        } else {
            let prev_max = max_seq(a.subrange(0, i));
            if a[i] >= prev_max { a[i] } else { prev_max }
        }
    decreases i
{
    if i == 0 {
        assert(a.subrange(0, 1).len() == 1);
        assert(a.subrange(0, 1)[0] == a[0]);
    } else {
        assert(a.subrange(0, i + 1).len() == i + 1);
        let prefix = a.subrange(0, i + 1).subrange(0, i);
        assert(prefix =~= a.subrange(0, i));
        assert(a.subrange(0, i + 1)[i] == a[i]);
    }
}

proof fn final_min_max_lemma(a: Seq<int>)
    requires a.len() > 0
    ensures 
        min_seq(a) == min_seq(a.subrange(0, a.len() as int)),
        max_seq(a) == max_seq(a.subrange(0, a.len() as int))
{
    assert(a.subrange(0, a.len() as int) =~= a);
}
// </vc-helpers>

// <vc-spec>
fn sum_min_max(a: &[i32]) -> (sum: i32)
    requires a.len() > 0
    ensures sum == max_seq(a@.map(|i: int, x: i32| x as int)) + min_seq(a@.map(|i: int, x: i32| x as int))
// </vc-spec>
// <vc-code>
{
    let ghost a_seq: Seq<int> = a@.map(|j: int, x: i32| x as int);
    
    let mut min_val: i32 = a[0];
    let mut max_val: i32 = a[0];
    let mut i: usize = 1;
    
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            min_val as int == min_seq(a_seq.subrange(0, i as int)),
            max_val as int == max_seq(a_seq.subrange(0, i as int)),
            a_seq =~= a@.map(|j: int, x: i32| x as int),
    {
        proof {
            min_seq_unfold(a_seq, i as int);
            max_seq_unfold(a_seq, i as int);
        }
        
        if a[i] < min_val {
            min_val = a[i];
        }
        
        if a[i] > max_val {
            max_val = a[i];
        }
        
        i = i + 1;
    }
    
    proof {
        final_min_max_lemma(a_seq);
        assert(a_seq =~= a@.map(|j: int, x: i32| x as int));
    }
    
    min_val + max_val
}
// </vc-code>

fn main() {}

}