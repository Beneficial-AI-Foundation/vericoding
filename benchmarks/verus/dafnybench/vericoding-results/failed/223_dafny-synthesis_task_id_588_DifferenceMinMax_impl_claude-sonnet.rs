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
proof fn min_max_properties(a: Seq<int>)
    requires a.len() > 0
    ensures 
        forall|i: int| 0 <= i < a.len() ==> #[trigger] min(a) <= #[trigger] a[i] && #[trigger] a[i] <= #[trigger] max(a)
    decreases a.len()
{
    if a.len() == 1 {
        // Base case: single element
    } else {
        let prefix = a.take(a.len() - 1);
        min_max_properties(prefix);
        // The recursive definition ensures the property holds
    }
}

proof fn min_max_extend(a: Seq<int>, x: int)
    requires a.len() > 0
    ensures 
        min(a.push(x)) == if x <= min(a) { x } else { min(a) },
        max(a.push(x)) == if x >= max(a) { x } else { max(a) }
{
    let extended = a.push(x);
    assert(extended.len() == a.len() + 1);
    assert(extended.take(extended.len() - 1) == a);
    assert(extended[extended.len() - 1] == x);
}

proof fn take_map_commute(a: Seq<i32>, n: int)
    requires 0 <= n <= a.len()
    ensures a.take(n).map(|i, x| x as int) == a.map(|i, x| x as int).take(n)
{
    // This property holds by definition
}
// </vc-helpers>

// <vc-spec>
fn difference_min_max(a: &[i32]) -> (diff: i32)
    requires a.len() > 0
    ensures diff == max(a@.map(|i, x| x as int)) - min(a@.map(|i, x| x as int))
// </vc-spec>
// <vc-code>
{
    let mut min_val = a[0];
    let mut max_val = a[0];
    
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            i > 0 ==> min_val as int == min(a@.take(i as int).map(|j, x| x as int)),
            i > 0 ==> max_val as int == max(a@.take(i as int).map(|j, x| x as int)),
            i == 0 ==> min_val == a[0] && max_val == a[0]
        decreases a.len() - i
    {
        let current_val = a[i];
        
        if i == 0 {
            min_val = current_val;
            max_val = current_val;
        } else {
            proof {
                take_map_commute(a@, i as int);
                let prev_seq = a@.take(i as int).map(|j, x| x as int);
                let curr_seq = a@.take((i + 1) as int).map(|j, x| x as int);
                assert(curr_seq == prev_seq.push(current_val as int));
                min_max_extend(prev_seq, current_val as int);
            }
            
            if current_val < min_val {
                min_val = current_val;
            }
            if current_val > max_val {
                max_val = current_val;
            }
        }
        i += 1;
    }
    
    proof {
        assert(i == a.len());
        take_map_commute(a@, a.len() as int);
        assert(a@.take(a.len() as int) == a@);
        assert(a@.map(|j, x| x as int) == a@.take(a.len() as int).map(|j, x| x as int));
    }
    
    max_val - min_val
}
// </vc-code>

fn main() {}

}