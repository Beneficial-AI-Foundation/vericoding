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
proof fn sum2_empty(v: Seq<i32>, i: int)
    requires 0 <= i <= v.len()
    ensures sum2(v, i, i) == 0
{
}

proof fn sum2_single(v: Seq<i32>, i: int)
    requires 0 <= i < v.len()
    ensures sum2(v, i, i + 1) == v[i] as int
{
}

proof fn sum2_extend_left(v: Seq<i32>, i: int, j: int)
    requires 0 <= i < j <= v.len()
    ensures sum2(v, i, j) == v[i] as int + sum2(v, i + 1, j)
    decreases j - i
{
}

proof fn sum2_split(v: Seq<i32>, i: int, k: int, j: int)
    requires 0 <= i <= k <= j <= v.len()
    ensures sum2(v, i, j) == sum2(v, i, k) + sum2(v, k, j)
    decreases j - i
{
    if i == k {
        assert(sum2(v, i, i) == 0);
    } else {
        assert(sum2(v, i, j) == v[i] as int + sum2(v, i + 1, j));
        sum2_split(v, i + 1, k, j);
        assert(sum2(v, i + 1, j) == sum2(v, i + 1, k) + sum2(v, k, j));
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
    let mut max_sum: i32 = v[i];
    let mut max_start: usize = i;
    let mut current_sum: i32 = v[i];
    let mut j: usize = i;
    
    proof {
        sum2_single(v@, i as int);
        assert(sum2(v@, i as int, (i + 1) as int) == v@[i as int] as int);
        assert(sum2(v@, max_start as int, (i + 1) as int) == max_sum as int);
        assert forall|l: int, ss: int| i as int <= l <= i as int && ss == (i + 1) as int implies
            sum2(v@, l, ss) <= max_sum as int by {
            assert(l == i as int);
            assert(sum2(v@, l, ss) == v@[i as int] as int);
        }
    }
    
    while j > 0
        invariant
            j <= i,
            current_sum as int == sum2(v@, j as int, (i + 1) as int),
            max_start <= i,
            max_start >= j,
            max_sum as int == sum2(v@, max_start as int, (i + 1) as int),
            forall|l: int, ss: int| j <= l <= i && ss == (i + 1) as int ==> 
                #[trigger] sum2(v@, l, ss) <= max_sum as int,
        decreases j
    {
        j = j - 1;
        let old_current_sum = current_sum;
        let old_max_sum = max_sum;
        let old_max_start = max_start;
        
        current_sum = v[j] + current_sum;
        
        proof {
            let old_j = (j + 1) as int;
            sum2_extend_left(v@, j as int, (i + 1) as int);
            assert(current_sum as int == v@[j as int] as int + sum2(v@, old_j, (i + 1) as int));
            assert(current_sum as int == sum2(v@, j as int, (i + 1) as int));
        }
        
        if current_sum > max_sum {
            max_sum = current_sum;
            max_start = j;
            
            proof {
                let old_j = (j + 1) as int;
                assert(max_sum as int == sum2(v@, max_start as int, (i + 1) as int));
                assert forall|l: int, ss: int| j <= l <= i && ss == (i + 1) as int implies
                    sum2(v@, l, ss) <= max_sum as int by {
                    if l == j as int {
                        assert(sum2(v@, l, ss) == current_sum as int);
                        assert(sum2(v@, l, ss) == max_sum as int);
                    } else {
                        assert(old_j <= l <= i);
                        assert(sum2(v@, l, ss) <= old_max_sum as int);
                        assert(old_max_sum < max_sum);
                    }
                }
            }
        } else {
            proof {
                let old_j = (j + 1) as int;
                assert(max_sum as int == sum2(v@, max_start as int, (i + 1) as int));
                assert forall|l: int, ss: int| j <= l <= i && ss == (i + 1) as int implies
                    sum2(v@, l, ss) <= max_sum as int by {
                    if l == j as int {
                        assert(sum2(v@, l, ss) == current_sum as int);
                        assert(current_sum <= max_sum);
                    } else {
                        assert(old_j <= l <= i);
                        assert(sum2(v@, l, ss) <= old_max_sum as int);
                        assert(old_max_sum == max_sum);
                    }
                }
            }
        }
    }
    
    proof {
        assert(j == 0);
        assert forall|l: int, ss: int| 0 <= l <= i && ss == (i + 1) as int implies
            sum2(v@, l, ss) <= max_sum as int by {
            assert(j <= l <= i);
        }
        assert(sum_max_to_right2(v@, 0, i as int, max_sum as int));
    }
    
    (max_sum, max_start)
}
// </vc-code>

fn main() {}

}