use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Sum2(v: Vec<int>, start: int, end: int) -> int
    decreases end - start
{
    if start >= end {
        0
    } else {
        v[start] + Sum2(v, start + 1, end)
    }
}

spec fn SumMaxToRight2(v: Vec<int>, start: int, end: int, max_sum: int) -> bool {
    forall|k: int| start <= k <= end ==> Sum2(v, k, end + 1) <= max_sum
}

fn segSumaMaxima2(v: Vec<int>, i: int) -> (s: int, k: int)
    requires
        v.len() > 0 && 0 <= i < v.len()
    ensures
        0 <= k <= i && s == Sum2(v, k, i + 1) && SumMaxToRight2(v, 0, i, s)
{
    let mut max_sum = v[i as usize];
    let mut best_start = i;
    let mut current_sum = v[i as usize];
    
    if i == 0 {
        return (max_sum, best_start);
    }
    
    let mut j = i - 1;
    while j >= 0
        invariant
            -1 <= j < i,
            current_sum == Sum2(v, j + 1, i + 1),
            max_sum == Sum2(v, best_start, i + 1),
            j + 1 <= best_start <= i,
            forall|k: int| j + 1 <= k <= i ==> Sum2(v, k, i + 1) <= max_sum
    {
        current_sum = current_sum + v[j as usize];
        
        if current_sum > max_sum {
            max_sum = current_sum;
            best_start = j;
        }
        
        if j == 0 {
            break;
        }
        j = j - 1;
    }
    
    // When we exit the loop, j is either -1 (if we decremented all the way) or 0 (if we broke)
    // In both cases, we have checked all positions from 0 to i
    assert(j == -1 || j == 0);
    assert(forall|k: int| 0 <= k <= i ==> Sum2(v, k, i + 1) <= max_sum);
    
    (max_sum, best_start)
}

}