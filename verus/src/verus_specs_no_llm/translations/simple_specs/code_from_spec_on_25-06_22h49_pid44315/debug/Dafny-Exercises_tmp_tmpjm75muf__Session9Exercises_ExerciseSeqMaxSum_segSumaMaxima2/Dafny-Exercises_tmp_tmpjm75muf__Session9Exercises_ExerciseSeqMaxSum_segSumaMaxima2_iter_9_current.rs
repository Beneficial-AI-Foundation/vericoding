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
    
    if i == 0 {
        // Prove that SumMaxToRight2 holds for the base case
        assert(Sum2(v, 0, 1) == v[0]) by {
            assert(Sum2(v, 0, 1) == v[0] + Sum2(v, 1, 1));
            assert(Sum2(v, 1, 1) == 0);
        };
        assert(SumMaxToRight2(v, 0, 0, max_sum)) by {
            assert(forall|k: int| 0 <= k <= 0 ==> Sum2(v, k, 1) <= max_sum);
            assert(Sum2(v, 0, 1) == v[0]);
        };
        return (max_sum, best_start);
    }
    
    let mut j = i - 1;
    let mut current_sum = v[i as usize];
    
    while j >= 0
        invariant
            -1 <= j < i,
            0 <= i < v.len(),
            current_sum == Sum2(v, j + 1, i + 1),
            max_sum == Sum2(v, best_start, i + 1),
            j + 1 <= best_start <= i,
            forall|k: int| j + 1 <= k <= i ==> Sum2(v, k, i + 1) <= max_sum,
        decreases j + 1
    {
        // Establish bounds for array access
        assert(0 <= j < v.len());
        assert(0 <= j < i < v.len());
        
        let old_current_sum = current_sum;
        current_sum = current_sum + v[j as usize];
        
        // Prove that current_sum equals Sum2(v, j, i + 1)
        assert(current_sum == Sum2(v, j, i + 1)) by {
            assert(Sum2(v, j, i + 1) == v[j] + Sum2(v, j + 1, i + 1));
            assert(old_current_sum == Sum2(v, j + 1, i + 1));
            assert(current_sum == old_current_sum + v[j]);
        };
        
        if current_sum > max_sum {
            max_sum = current_sum;
            best_start = j;
            
            // Update the invariant after assignment
            assert(forall|k: int| j <= k <= i ==> Sum2(v, k, i + 1) <= max_sum) by {
                // Previous invariant ensures j+1 <= k <= i case
                assert(forall|k: int| j + 1 <= k <= i ==> Sum2(v, k, i + 1) <= max_sum);
                // New max_sum >= current_sum = Sum2(v, j, i + 1)
                assert(Sum2(v, j, i + 1) <= max_sum);
                assert(forall|k: int| {
                    if j + 1 <= k <= i {
                        Sum2(v, k, i + 1) <= current_sum
                    } else if k == j {
                        Sum2(v, k, i + 1) == current_sum
                    } else {
                        true
                    }
                });
            };
        } else {
            // Prove the invariant is maintained when max_sum doesn't change
            assert(forall|k: int| j <= k <= i ==> Sum2(v, k, i + 1) <= max_sum) by {
                assert(forall|k: int| j + 1 <= k <= i ==> Sum2(v, k, i + 1) <= max_sum);
                assert(Sum2(v, j, i + 1) == current_sum);
                assert(current_sum <= max_sum);
                assert(forall|k: int| {
                    if j + 1 <= k <= i {
                        Sum2(v, k, i + 1) <= max_sum
                    } else if k == j {
                        Sum2(v, k, i + 1) <= max_sum
                    } else {
                        true
                    }
                });
            };
        }
        
        j = j - 1;
    }
    
    // After the loop, j == -1, so we have proven forall k in [0, i]
    assert(j == -1);
    assert(forall|k: int| 0 <= k <= i ==> Sum2(v, k, i + 1) <= max_sum) by {
        assert(forall|k: int| j + 1 <= k <= i ==> Sum2(v, k, i + 1) <= max_sum);
        assert(j + 1 == 0);
    };
    assert(SumMaxToRight2(v, 0, i, max_sum)) by {
        assert(forall|k: int| 0 <= k <= i ==> Sum2(v, k, i + 1) <= max_sum);
    };
    
    (max_sum, best_start)
}

}