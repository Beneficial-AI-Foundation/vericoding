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
proof lemma_sum_eq_sum2(v: Seq<int>, i: int, j: int)
    requires
        0 <= i <= j <= v.len(),
    ensures
        sum(v, i, j) == sum2(v, i, j),
    decreases j - i
{
    if i < j {
        lemma_sum_eq_sum2(v, i, j-1);
        assert(sum(v, i, j) == sum(v, i, j-1) + v[j-1]);
        lemma_sum_eq_sum2(v, i+1, j);
        assert(sum2(v, i, j) == v[i] + sum2(v, i+1, j));
        assert(sum(v, i, j-1) == sum2(v, i, j-1));
        assert(sum(v, i+1, j) == sum2(v, i+1, j));
    }
}

proof lemma_sum_split(v: Seq<int>, i: int, k: int, j: int)
    requires
        0 <= i <= k <= j <= v.len(),
    ensures
        sum(v, i, j) == sum(v, i, k) + sum(v, k, j),
        sum2(v, i, j) == sum2(v, i, k) + sum2(v, k, j)
    decreases j - i
{
    if i < k {
        lemma_sum_split(v, i, k, j-1);
    } else if k < j {
        lemma_sum_split(v, i+1, k, j);
    }
}

proof lemma_sum_max_to_right_implies(v: Seq<int>, i: int, s: int, j: int)
    requires
        0 <= j <= i < v.len(),
        sum_max_to_right(v, i, s),
    ensures
        sum_max_to_right2(v, j, i, s)
{
    assert forall|l: int, ss: int| j <= l <= i && ss == i + 1 implies sum2(v, l, ss) <= s by {
        lemma_sum_eq_sum2(v, l, ss);
        assert(sum(v, l, ss) == sum2(v, l, ss));
    };
}

proof lemma_sum_max_to_right2_cons(v: Seq<int>, j: int, i: int, s: int)
    requires
        0 <= j <= i < v.len(),
        sum_max_to_right2(v, j, i, s),
    ensures
        sum2(v, j, i+1) <= s
{
    assert(j <= j <= i);
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
    let mut max_sum = v[i];
    let mut max_end = i;
    let mut current_sum = v[i] as int;
    let mut current_start = i;
    
    proof {
        lemma_sum_eq_sum2(v@.map_values(|x: i32| x as int), i as int, (i+1) as int);
    }
    
    let mut idx = i;
    while idx > 0
        invariant
            idx <= i,
            current_start >= idx,
            current_start <= i,
            current_sum == sum2(v@.map_values(|x: i32| x as int), current_start as int, (i+1) as int),
            max_sum as int == sum2(v@.map_values(|x: i32| x as int), max_end as int, (i+1) as int),
            forall|k: int| idx <= k <= i ==> sum2(v@.map_values(|x: i32| x as int), k as int, (i+1) as int) <= max_sum as int,
        decreases idx
    {
        idx = idx - 1;
        current_sum = current_sum + v[idx] as int;
        
        proof {
            lemma_sum_eq_sum2(v@.map_values(|x: i32| x as int), idx as int, (i+1) as int);
        }
        
        if current_sum > max_sum as int {
            max_sum = current_sum as i32;
            max_end = idx;
        } else {
            current_start = idx + 1;
            current_sum = max_sum as int;
        }
        
        proof {
            assert forall|k: int| idx <= k <= i implies sum2(v@.map_values(|x: i32| x as int), k as int, (i+1) as int) <= max_sum as int by {
                if k == idx {
                    assert(sum2(v@.map_values(|x: i32| x as int), idx as int, (i+1) as int) == current_sum);
                } else {
                    // k > idx, so it was true in previous iteration
                }
            };
        }
    }
    
    proof {
        lemma_sum_eq_sum2(v@.map_values(|x: i32| x as int), max_end as int, (i+1) as int);
        lemma_sum_max_to_right_implies(v@.map_values(|x: i32| x as int), i as int, max_sum as int, 0);
    }
    
    (max_sum, max_end)
}
// </vc-code>

fn main() {
}

}