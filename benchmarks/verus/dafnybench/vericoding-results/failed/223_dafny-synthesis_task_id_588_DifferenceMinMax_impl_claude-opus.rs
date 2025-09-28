use vstd::prelude::*;

verus! {

// The order of the recursion in these two functions
// must match the order of the iteration in the algorithm above
spec fn min(a: Seq<int>) -> int
    recommends a.len() > 0
    decreases a.len() when a.len() > 0
{
    if a.len() == 1 {
        a[0]
    } else {
        let prefix = a.take(a.len() - 1);
        let min_prefix = min(prefix);
        if a[a.len() - 1] <= min_prefix {
            a[a.len() - 1]
        } else {
            min_prefix
        }
    }
}

spec fn max(a: Seq<int>) -> int
    recommends a.len() > 0  
    decreases a.len() when a.len() > 0
{
    if a.len() == 1 {
        a[0]
    } else {
        let prefix = a.take(a.len() - 1);
        let max_prefix = max(prefix);
        if a[a.len() - 1] >= max_prefix {
            a[a.len() - 1]
        } else {
            max_prefix
        }
    }
}

// <vc-helpers>
// Helper lemmas to relate partial computations to the recursive definitions
proof fn min_prefix_property(a: Seq<int>, k: int)
    requires 
        0 < k <= a.len(),
    ensures 
        min(a.take(k)) == min(a.take(k - 1).push(a[k - 1])),
    decreases k,
{
    assert(a.take(k) =~= a.take(k - 1).push(a[k - 1]));
}

proof fn max_prefix_property(a: Seq<int>, k: int)
    requires 
        0 < k <= a.len(),
    ensures 
        max(a.take(k)) == max(a.take(k - 1).push(a[k - 1])),
    decreases k,
{
    assert(a.take(k) =~= a.take(k - 1).push(a[k - 1]));
}

// Helper to establish that min/max computations match the recursive definition
proof fn min_update(a: Seq<int>, k: int, current_min: int, next_val: int)
    requires
        0 < k < a.len(),
        current_min == min(a.take(k)),
        next_val == a[k],
    ensures
        if next_val <= current_min { next_val } else { current_min } == min(a.take(k + 1)),
{
    min_prefix_property(a, k + 1);
    assert(a.take(k + 1) =~= a.take(k).push(a[k]));
}

proof fn max_update(a: Seq<int>, k: int, current_max: int, next_val: int)
    requires
        0 < k < a.len(),
        current_max == max(a.take(k)),
        next_val == a[k],
    ensures
        if next_val >= current_max { next_val } else { current_max } == max(a.take(k + 1)),
{
    max_prefix_property(a, k + 1);
    assert(a.take(k + 1) =~= a.take(k).push(a[k]));
}
// </vc-helpers>

// <vc-spec>
fn difference_min_max(a: &[i32]) -> (diff: i32)
    requires a.len() > 0
    ensures diff == max(a@.map(|i, x| x as int)) - min(a@.map(|i, x| x as int))
// </vc-spec>
// <vc-code>
{
    let ghost a_seq = a@.map(|i, x| x as int);
    let mut min_val = a[0];
    let mut max_val = a[0];
    
    assert(a_seq.take(1) =~= seq![a_seq[0]]);
    assert(min(a_seq.take(1)) == a_seq[0]);
    assert(max(a_seq.take(1)) == a_seq[0]);
    
    let mut i: usize = 1;
    while i < a.len()
        invariant 
            1 <= i <= a.len(),
            min_val as int == min(a_seq.take(i as int)),
            max_val as int == max(a_seq.take(i as int)),
            min_val <= max_val,
            i32::MIN <= min_val <= i32::MAX,
            i32::MIN <= max_val <= i32::MAX,
            (max_val as int) - (min_val as int) <= i32::MAX,
            (max_val as int) - (min_val as int) >= i32::MIN,
        decreases a.len() - i,
    {
        let old_min = min_val;
        let old_max = max_val;
        
        if a[i] < min_val {
            min_val = a[i];
        }
        
        if a[i] > max_val {
            max_val = a[i];
        }
        
        proof {
            min_update(a_seq, i as int, old_min as int, a_seq[i as int]);
            max_update(a_seq, i as int, old_max as int, a_seq[i as int]);
            assert(min_val <= max_val);
        }
        
        i = i + 1;
    }
    
    proof {
        assert(a_seq.take(a.len() as int) =~= a_seq);
    }
    
    max_val - min_val
}
// </vc-code>

fn main() {}

}