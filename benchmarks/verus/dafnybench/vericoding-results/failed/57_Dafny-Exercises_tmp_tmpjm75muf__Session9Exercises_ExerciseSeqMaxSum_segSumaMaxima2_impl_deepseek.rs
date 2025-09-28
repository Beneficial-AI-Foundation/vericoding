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
proof fn sum_equals_sum2(v: Seq<i32>, i: int, j: int)
    requires
        0 <= i <= j <= v.len(),
    ensures
        sum(v, i, j) == sum2(v, i, j),
    decreases j - i
{
    if i < j {
        sum_equals_sum2(v, i, j - 1);
        assert(sum(v, i, j) == sum(v, i, j - 1) + v[j - 1] as int);
        sum_equals_sum2(v, i + 1, j);
        assert(sum2(v, i, j) == v[i] as int + sum2(v, i + 1, j));
    }
}

proof fn sum_max_to_right_equivalent(v: Seq<i32>, i: int, s: int)
    requires
        0 <= i < v.len(),
    ensures
        sum_max_to_right(v, i, s) == sum_max_to_right2(v, 0, i, s)
{
    assert forall|l: int, ss: int| 0 <= l <= i && ss == i + 1 implies sum(v, l, ss) <= s by {
        sum_equals_sum2(v, l, ss);
    };
    assert forall|l: int, ss: int| 0 <= l <= i && ss == i + 1 implies sum2(v, l, ss) <= s by {
        sum_equals_sum2(v, l, ss);
    };
}

proof fn sum2_split(v: Seq<i32>, i: int, k: int, j: int)
    requires
        0 <= i <= k <= j <= v.len(),
    ensures
        sum2(v, i, j) == sum2(v, i, k) + sum2(v, k, j)
    decreases j - i
{
    if i < k {
        assert(sum2(v, i, j) == v[i] as int + sum2(v, i + 1, j));
        sum2_split(v, i + 1, k, j);
        assert(sum2(v, i, j) == v[i] as int + sum2(v, i + 1, k) + sum2(v, k, j));
        assert(sum2(v, i, k) == v[i] as int + sum2(v, i + 1, k));
    }
}

proof fn lemma_sum2_monotonic_right(v: Seq<i32>, l1: int, l2: int, r: int)
    requires
        0 <= l1 <= l2 <= r <= v.len(),
    ensures
        sum2(v, l2, r) <= sum2(v, l1, r)
{
    if l1 < l2 {
        lemma_sum2_monotonic_right(v, l1 + 1, l2, r);
        assert(sum2(v, l1, r) == v[l1] as int + sum2(v, l1 + 1, r));
    }
}

proof fn lemma_sum2_empty_range(v: Seq<i32>, i: int, j: int)
    requires
        0 <= i <= j <= v.len(),
    ensures
        sum2(v, i, i) == 0,
        i == j ==> sum2(v, i, j) == 0
{
}

proof fn lemma_sum2_single_element(v: Seq<i32>, i: int)
    requires
        0 <= i < v.len(),
    ensures
        sum2(v, i, i + 1) == v[i] as int
{
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
    let mut max_end = i;
    let mut current_sum = v[i];
    let mut current_end = i;
    
    proof {
        sum_equals_sum2(v@, i as int, (i + 1) as int);
        sum_max_to_right_equivalent(v@, i as int, max_sum as int);
        lemma_sum2_single_element(v@, i as int);
        assert(sum2(v@, i as int, (i + 1) as int) == v[i] as int);
        assert(sum_max_to_right2(v@, 0, i as int, max_sum as int));
    }
    
    let mut j = i;
    while j > 0 {
        invariant
            0 <= j <= i,
            current_end == j,
            j <= i,
            current_sum as int == sum2(v@, j as int, (i + 1) as int),
            max_sum as int == sum2(v@, max_end as int, (i + 1) as int),
            sum_max_to_right2(v@, j as int, i as int, max_sum as int),
        decreases j
    {
        j = j - 1;
        current_sum = current_sum + v[j];
        current_end = j;
        
        proof {
            lemma_sum2_split(v@, j as int, (j + 1) as int, (i + 1) as int);
            assert(sum2(v@, j as int, (i + 1) as int) == v[j] as int + sum2(v@, (j + 1) as int, (i + 1) as int));
            assert(current_sum as int == sum2(v@, j as int, (i + 1) as int));
        }
        
        if current_sum >= max_sum {
            max_sum = current_sum;
            max_end = j;
            
            proof {
                assert forall|l: int, ss: int| j <= l <= i && ss == i + 1 implies sum2(v@, l, ss) <= max_sum as int by {
                    lemma_sum2_monotonic_right(v@, j as int, l, (i + 1) as int);
                    assert(sum2(v@, l, i + 1) <= sum2(v@, j, i + 1));
                    assert(sum2(v@, j, i + 1) == current_sum as int);
                };
            }
        } else {
            proof {
                assert forall|l: int, ss: int| j <= l <= i && ss == i + 1 implies sum2(v@, l, ss) <= max_sum as int by {
                    if l == j {
                        assert(sum2(v@, j, i + 1) == current_sum as int);
                    } else {
                        assert(l > j);
                        assert(sum2(v@, l, i + 1) <= max_sum as int) by {
                            assert(sum_max_to_right2(v@, (j + 1) as int, i as int, max_sum as int));
                        }
                    }
                };
            }
        }
    }
    
    (max_sum, max_end)
}
// </vc-code>

fn main() {}

}