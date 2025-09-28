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
proof fn lemma_min_seq_step(a: Seq<int>, i: usize)
    requires 0 < i < a.len()
    ensures min_seq(a.subrange(0, i as int + 1)) == if a[i as int] <= min_seq(a.subrange(0, i as int)) { a[i as int] } else { min_seq(a.subrange(0, i as int)) }
{
    let prefix = a.subrange(0, i as int);
    let full = a.subrange(0, i as int + 1);
    assert(full == prefix.push(a[i as int]));
    assert(full.len() == prefix.len() + 1);
    assert(full[full.len() - 1] == a[i as int]);
}

proof fn lemma_max_seq_step(a: Seq<int>, i: usize)
    requires 0 < i < a.len()
    ensures max_seq(a.subrange(0, i as int + 1)) == if a[i as int] >= max_seq(a.subrange(0, i as int)) { a[i as int] } else { max_seq(a.subrange(0, i as int)) }
{
    let prefix = a.subrange(0, i as int);
    let full = a.subrange(0, i as int + 1);
    assert(full == prefix.push(a[i as int]));
    assert(full.len() == prefix.len() + 1);
    assert(full[full.len() - 1] == a[i as int]);
}
// </vc-helpers>

// <vc-spec>
fn sum_min_max(a: &[i32]) -> (sum: i32)
    requires a.len() > 0
    ensures sum == max_seq(a@.map(|i: int, x: i32| x as int)) + min_seq(a@.map(|i: int, x: i32| x as int))
// </vc-spec>
// <vc-code>
{
    let mut min_val = a[0];
    let mut max_val = a[0];
    let mut i = 1;
    
    let ghost seq_a = a@.map(|i: int, x: i32| x as int);
    
    while i < a.len()
        invariant 
            1 <= i <= a.len(),
            min_val as int == min_seq(seq_a.subrange(0, i as int)),
            max_val as int == max_seq(seq_a.subrange(0, i as int))
    {
        proof {
            lemma_min_seq_step(seq_a, i);
            lemma_max_seq_step(seq_a, i);
        }
        
        if a[i] < min_val {
            min_val = a[i];
        }
        if a[i] > max_val {
            max_val = a[i];
        }
        i += 1;
    }
    
    proof {
        assert(seq_a.subrange(0, i as int) == seq_a);
    }
    
    min_val + max_val
}
// </vc-code>

fn main() {}

}