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
proof fn lemma_sum_monotonic(v: Seq<int>, i: int, j: int, k: int)
    requires 0 <= i <= j <= k <= v.len()
    ensures sum(v, i, j) <= sum(v, i, k)
    decreases k - j
{
    if j == k {
    } else {
        lemma_sum_monotonic(v, i, j + 1, k);
        assert(sum(v, i, j) + sum(v, j, j + 1) == sum(v, i, j + 1));
    }
}

proof fn lemma_sum2_monotonic(v: Seq<int>, i: int, j: int, k: int)
    requires 0 <= i <= j <= k <= v.len()
    ensures sum2(v, i, j) <= sum2(v, i, k)
    decreases k - j
{
    if j == k {
    } else {
        lemma_sum2_monotonic(v, i, j + 1, k);
        assert(sum2(v, i, j) + sum2(v, j, j + 1) == sum2(v, i, j + 1));
    }
}

proof fn lemma_sum_max_to_right_implies_sum2(v: Seq<int>, i: int, j: int, s: int)
    requires 0 <= i < j < v.len()
    requires sum_max_to_right(v, i, s)
    ensures sum2(v, i, j) <= s
    decreases j - i
{
    if i + 1 == j {
        assert(sum(v, i, j) == v[i]);
        assert(sum_max_to_right(v, i, s) ==> v[i] <= s);
    } else {
        lemma_sum_max_to_right_implies_sum2(v, i + 1, j, s);
        lemma_sum2_monotonic(v, i, i + 1, j);
        assert(sum(v, i, i + 1) <= s);
    }
}

proof fn lemma_sum2_implies_sum_max_to_right(v: Seq<int>, i: int, s: int)
    requires 0 <= i < v.len()
    requires forall|k: int| 0 <= k <= i ==> sum2(v, k, i + 1) <= s
    ensures sum_max_to_right(v, i, s)
{
    assert forall|l: int, ss: int| 0 <= l <= i && ss == i + 1 implies sum(v, l, ss) <= s by {
        assert(sum(v, l, ss) == sum2(v, l, ss));
    }
}

proof fn lemma_sum_equals_sum2(v: Seq<int>, i: int, j: int)
    requires 0 <= i <= j <= v.len()
    ensures sum(v, i, j) == sum2(v, i, j)
    decreases j - i
{
    if i == j {
    } else {
        lemma_sum_equals_sum2(v, i, j - 1);
        assert(sum(v, i, j - 1) + v[j - 1] == sum(v, i, j));
        assert(sum2(v, i, j - 1) + v[j - 1] == sum2(v, i, j));
    }
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
    let mut current_sum = v[i];
    let mut max_sum = v[i];
    let mut best_j = i;
    let mut j = i;
    
    let v_int = v@.map_values(|x: i32| x as int);
    
    proof {
        lemma_sum_equals_sum2(v_int, best_j as int, (i+1) as int);
        lemma_sum2_implies_sum_max_to_right(v_int, i as int, max_sum as int);
    }

    while j > 0
        invariant
            0 <= j <= i,
            current_sum == sum2(v_int, j as int, (i+1) as int),
            max_sum == sum2(v_int, best_j as int, (i+1) as int),
            forall|k: int| j <= k <= i ==> sum2(v_int, k, (i+1) as int) <= max_sum,
            sum_max_to_right(v_int, i as int, max_sum as int)
    {
        j = j - 1;
        current_sum = current_sum + v[j];
        
        if current_sum > max_sum {
            max_sum = current_sum;
            best_j = j;
        }
        
        proof {
            lemma_sum2_monotonic(v_int, j as int, (j+1) as int, (i+1) as int);
            lemma_sum_equals_sum2(v_int, best_j as int, (i+1) as int);
            lemma_sum2_implies_sum_max_to_right(v_int, i as int, max_sum as int);
        }
    }

    (max_sum, best_j)
}
// </vc-code>

fn main() {
}

}