use vstd::prelude::*;

verus! {

spec fn sum(v: Seq<i32>, i: int, j: int) -> int
    recommends 0 <= i <= j <= v.len()
    decreases j - i when i < j
{
    if i == j {
        0
    } else {
        sum(v, i, (j - 1) as int) + v[(j - 1) as int] as int
    }
}

spec fn sum_max_to_right(v: Seq<i32>, i: int, s: int) -> bool
    recommends 0 <= i < v.len()
{
    forall|l: int, ss: int| 0 <= l <= i && ss == i + 1 ==> sum(v, l, ss) <= s
}



spec fn sum2(v: Seq<i32>, i: int, j: int) -> int
    recommends 0 <= i <= j <= v.len()
    decreases j - i when i < j
{
    if i == j {
        0
    } else {
        v[i] as int + sum2(v, i + 1, j)
    }
}

//Now do the same but with a loop from right to left
spec fn sum_max_to_right2(v: Seq<i32>, j: int, i: int, s: int) -> bool //maximum sum stuck to the right
    recommends 0 <= j <= i < v.len()
{
    forall|l: int, ss: int| j <= l <= i && ss == i + 1 ==> sum2(v, l, ss) <= s
}

// <vc-helpers>
proof fn lemma_sum2_add_left(v: Seq<i32>, i: int, j: int)
    requires 0 <= i < j <= v.len()
    ensures sum2(v, i, j) == v[i] as int + sum2(v, i + 1, j)
{
    // This follows directly from the definition of sum2
}

proof fn lemma_sum2_singleton(v: Seq<i32>, i: int)
    requires 0 <= i < v.len()
    ensures sum2(v, i, i + 1) == v[i] as int
{
    // This follows from the definition: sum2(v, i, i+1) = v[i] + sum2(v, i+1, i+1) = v[i] + 0
}

proof fn lemma_sum2_monotonic(v: Seq<i32>, i: int, j: int, k: int)
    requires 0 <= i <= j <= k <= v.len()
    ensures sum2(v, i, j) + sum2(v, j, k) == sum2(v, i, k)
    decreases k - i
{
    if i == j {
        // sum2(v, i, j) == 0, so we need sum2(v, j, k) == sum2(v, i, k)
        assert(sum2(v, i, j) == 0);
    } else if j == k {
        // sum2(v, j, k) == 0, so we need sum2(v, i, j) == sum2(v, i, k)
        assert(sum2(v, j, k) == 0);
    } else {
        // Inductive case: sum2(v, i, j) + sum2(v, j, k) == sum2(v, i, k)
        // By definition: sum2(v, i, k) = v[i] + sum2(v, i+1, k)
        // We want to show: sum2(v, i, j) + sum2(v, j, k) = v[i] + sum2(v, i+1, k)
        // By IH: sum2(v, i+1, j) + sum2(v, j, k) = sum2(v, i+1, k)
        // And: sum2(v, i, j) = v[i] + sum2(v, i+1, j)
        lemma_sum2_monotonic(v, i + 1, j, k);
        lemma_sum2_add_left(v, i, j);
        lemma_sum2_add_left(v, i, k);
    }
}

proof fn lemma_sum_max_to_right2_property(v: Seq<i32>, j: int, i: int, s: int, new_s: int, new_i: int)
    requires 
        0 <= j <= new_i <= i < v.len(),
        sum_max_to_right2(v, j, i, s),
        new_s as int == sum2(v, new_i as int, (i + 1) as int),
        new_s >= s
    ensures sum_max_to_right2(v, j, i, new_s)
{
    assert forall|l: int, ss: int| j <= l <= i && ss == i + 1 implies sum2(v, l, ss) <= new_s by {
        if j <= l <= i && ss == i + 1 {
            if l >= new_i {
                lemma_sum2_monotonic(v, new_i, l, ss);
                assert(sum2(v, l, ss) <= sum2(v, new_i, ss));
                assert(sum2(v, new_i, ss) == new_s);
            } else {
                assert(sum2(v, l, ss) <= s);
                assert(s <= new_s);
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn seg_suma_maxima2(v: &[i32], i: usize) -> (result: (i32, usize))
    requires v.len() > 0 && i < v.len()
    ensures 
        0 <= result.1 <= i && 
        result.0 as int == sum2(v@, result.1 as int, (i + 1) as int) && 
        sum_max_to_right2(v@, 0, i as int, result.0 as int)
//Implement and verify
// </vc-spec>
// <vc-code>
{
    let mut max_sum = v[i];
    let mut best_start = i;
    let mut current_sum = v[i];
    
    proof {
        lemma_sum2_singleton(v@, i as int);
        assert(sum2(v@, i as int, (i + 1) as int) == v@[i as int] as int);
    }
    
    if i == 0 {
        return (max_sum, best_start);
    }
    
    let mut j = i - 1;
    
    while j > 0
        invariant
            0 < j <= i - 1,
            0 <= best_start <= i,
            max_sum as int == sum2(v@, best_start as int, (i + 1) as int),
            current_sum as int == sum2(v@, (j + 1) as int, (i + 1) as int),
            sum_max_to_right2(v@, (j + 1) as int, i as int, max_sum as int)
        decreases j
    {
        current_sum = current_sum + v[j];
        
        proof {
            lemma_sum2_add_left(v@, j as int, (i + 1) as int);
            assert(sum2(v@, j as int, (i + 1) as int) == v@[j as int] as int + sum2(v@, (j + 1) as int, (i + 1) as int));
        }
        
        if current_sum >= max_sum {
            max_sum = current_sum;
            best_start = j;
            
            proof {
                lemma_sum_max_to_right2_property(v@, (j + 1) as int, i as int, max_sum as int, current_sum as int, j as int);
            }
        }
        
        j = j - 1;
    }
    
    // Handle j == 0 case
    current_sum = current_sum + v[0];
    
    proof {
        lemma_sum2_add_left(v@, 0, (i + 1) as int);
        assert(sum2(v@, 0, (i + 1) as int) == v@[0] as int + sum2(v@, 1, (i + 1) as int));
    }
    
    if current_sum >= max_sum {
        max_sum = current_sum;
        best_start = 0;
    }
    
    proof {
        assert forall|l: int, ss: int| 0 <= l <= i && ss == i + 1 implies sum2(v@, l, ss) <= max_sum as int by {
            if 0 <= l <= i && ss == i + 1 {
                if l == 0 {
                    assert(sum2(v@, l, ss) == current_sum as int);
                    assert(current_sum <= max_sum);
                } else {
                    assert(sum_max_to_right2(v@, 1, i as int, max_sum as int));
                    assert(1 <= l <= i);
                    assert(sum2(v@, l, ss) <= max_sum as int);
                }
            }
        }
    }
    
    (max_sum, best_start)
}
// </vc-code>

fn main() {}

}