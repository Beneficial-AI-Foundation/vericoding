use vstd::prelude::*;

verus! {

spec fn sum(v: Seq<int>, i: int, j: int) -> int
    recommends 0 <= i <= j <= v.len()
    decreases j when 0 <= i <= j <= v.len()
{
    if i == j {
        0 as int
    } else {
        sum(v, i, (j-1) as int) + v[(j-1) as int]
    }
}

spec fn sum_max_to_right(v: Seq<int>, i: int, s: int) -> bool
    recommends 0 <= i < v.len()
{
    forall|l: int, ss: int| 0 <= l <= i && ss == i + 1 ==> sum(v, l, ss) <= s
}

spec fn sum2(v: Seq<int>, i: int, j: int) -> int
    recommends 0 <= i <= j <= v.len()
    decreases j - i when 0 <= i <= j <= v.len()
{
    if i == j {
        0 as int
    } else {
        v[i as int] + sum2(v, (i+1) as int, j)
    }
}

spec fn sum_max_to_right2(v: Seq<int>, j: int, i: int, s: int) -> bool
    recommends 0 <= j <= i < v.len()
{
    forall|l: int, ss: int| j <= l <= i && ss == i + 1 ==> sum2(v, l, ss) <= s
}

// <vc-helpers>
proof fn sum_sum2_eq(v: Seq<int>, i: int, j: int)
    requires 0 <= i <= j <= v.len()
    ensures sum(v, i, j) == sum2(v, i, j)
    decreases j - i
{
    if i == j {
        // Base case: both are 0
    } else {
        // Recursive case
        sum_sum2_eq(v, i+1, j);
        
        // sum2(v, i, j) = v[i] + sum2(v, i+1, j) by definition
        // sum2(v, i+1, j) = sum(v, i+1, j) by recursive call
        // Need to show: sum(v, i, j) = v[i] + sum(v, i+1, j)
        
        // Prove sum(v, i, j) = v[i] + sum(v, i+1, j)
        sum_decompose_first(v, i, j);
        assert(sum(v, i, j) == v[i] + sum(v, i+1, j));
        assert(sum2(v, i, j) == v[i] + sum2(v, i+1, j));
        assert(sum2(v, i+1, j) == sum(v, i+1, j));
        assert(sum(v, i, j) == sum2(v, i, j));
    }
}

proof fn sum_decompose_first(v: Seq<int>, i: int, j: int)
    requires 0 <= i < j <= v.len()
    ensures sum(v, i, j) == v[i] + sum(v, i+1, j)
    decreases j - i
{
    if i + 1 == j {
        assert(sum(v, i, j) == sum(v, i, i) + v[i]);
        assert(sum(v, i, i) == 0);
        assert(sum(v, i+1, j) == 0);
        assert(sum(v, i, j) == v[i]);
    } else {
        sum_decompose_first(v, i, j-1);
        assert(sum(v, i, j) == sum(v, i, j-1) + v[j-1]);
        assert(sum(v, i, j-1) == v[i] + sum(v, i+1, j-1));
        assert(sum(v, i+1, j) == sum(v, i+1, j-1) + v[j-1]);
        assert(sum(v, i, j) == v[i] + sum(v, i+1, j));
    }
}

proof fn sum_decompose(v: Seq<int>, i: int, k: int, j: int)
    requires 0 <= i <= k <= j <= v.len()
    ensures sum(v, i, j) == sum(v, i, k) + sum(v, k, j)
    decreases j - k
{
    if k == j {
        assert(sum(v, k, j) == 0);
    } else {
        sum_decompose(v, i, k, j-1);
        assert(sum(v, i, j) == sum(v, i, j-1) + v[j-1]);
        assert(sum(v, k, j) == sum(v, k, j-1) + v[j-1]);
    }
}

proof fn sum_single(v: Seq<int>, i: int)
    requires 0 <= i < v.len()
    ensures sum(v, i, i+1) == v[i]
{
    assert(sum(v, i, i+1) == sum(v, i, i) + v[i]);
    assert(sum(v, i, i) == 0);
}
// </vc-helpers>

// <vc-spec>
fn seg_max_sum(v: &[i32], i: usize) -> (i32, usize)
    requires v.len() > 0 && i < v.len()
    ensures |result: (i32, usize)|
        result.1 <= i && 
        result.0 == sum(v@.map_values(|x: i32| x as int), result.1 as int, (i+1) as int) &&
        sum_max_to_right(v@.map_values(|x: i32| x as int), i as int, result.0 as int)
// </vc-spec>
// <vc-code>
{
    let mut max_sum = v[i] as i32;
    let mut max_start = i;
    let mut curr_sum = v[i] as i32;
    let mut curr_start = i;
    
    proof {
        let vv = v@.map_values(|x: i32| x as int);
        assert(curr_sum as int == sum2(vv, i as int, (i+1) as int));
        assert(sum2(vv, i as int, (i+1) as int) == vv[i as int]);
        assert(vv[i as int] == (v[i] as int));
    }
    
    let mut j = i;
    while j > 0
        invariant
            0 <= j <= i,
            j <= curr_start <= i,
            j <= max_start <= i,
            curr_start == j,
            curr_sum == sum2(v@.map_values(|x: i32| x as int), curr_start as int, (i+1) as int) as i32,
            max_sum == sum2(v@.map_values(|x: i32| x as int), max_start as int, (i+1) as int) as i32,
            sum_max_to_right2(v@.map_values(|x: i32| x as int), j as int, i as int, max_sum as int),
    {
        j = j - 1;
        
        let old_curr_sum = curr_sum;
        curr_sum = curr_sum + v[j] as i32;
        curr_start = j;
        
        proof {
            let vv = v@.map_values(|x: i32| x as int);
            assert(old_curr_sum as int == sum2(vv, (j+1) as int, (i+1) as int));
            assert(curr_sum as int == old_curr_sum as int + (v[j] as int));
            assert(sum2(vv, j as int, (i+1) as int) == vv[j as int] + sum2(vv, (j+1) as int, (i+1) as int));
            assert(vv[j as int] == (v[j] as int));
            assert(curr_sum as int == sum2(vv, j as int, (i+1) as int));
        }
        
        if curr_sum > max_sum {
            max_sum = curr_sum;
            max_start = j;
        }
        
        proof {
            let vv = v@.map_values(|x: i32| x as int);
            assert forall |l: int, ss: int| j <= l <= i && ss == i + 1 implies 
                sum2(vv, l, ss) <= max_sum as int by {
                if l == j {
                    assert(sum2(vv, l, ss) == curr_sum as int);
                    assert(curr_sum <= max_sum);
                } else {
                    assert(j < l <= i);
                    assert((j+1) <= l <= i);
                    assert(sum2(vv, l, ss) <= max_sum as int);
                }
            }
        }
    }
    
    proof {
        let vv = v@.map_values(|x: i32| x as int);
        sum_sum2_eq(vv, max_start as int, (i+1) as int);
        assert(sum(vv, max_start as int, (i+1) as int) == 
               sum2(vv, max_start as int, (i+1) as int));
        
        assert forall |l: int, ss: int| 0 <= l <= i && ss == i + 1 implies
            sum(vv, l, ss) <= max_sum as int by {
            sum_sum2_eq(vv, l, ss);
            assert(sum(vv, l, ss) == sum2(vv, l, ss));
            assert(sum2(vv, l, ss) <= max_sum as int);
        }
    }
    
    (max_sum, max_start)
}
// </vc-code>

fn main() {
}

}