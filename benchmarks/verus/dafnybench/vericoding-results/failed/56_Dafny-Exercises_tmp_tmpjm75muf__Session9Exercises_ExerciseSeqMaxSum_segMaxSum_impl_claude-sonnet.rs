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
proof fn lemma_sum_equivalence(v: Seq<int>, i: int, j: int)
    requires 0 <= i <= j <= v.len()
    ensures sum(v, i, j) == sum2(v, i, j)
    decreases j - i
{
    if i == j {
        // Base case: both are 0
    } else {
        lemma_sum_equivalence(v, i + 1, j);
        // sum(v, i, j) = sum(v, i, j-1) + v[j-1]
        // sum2(v, i, j) = v[i] + sum2(v, i+1, j)
        // We need to show these are equal
        lemma_sum_shift(v, i, j);
    }
}

proof fn lemma_sum_shift(v: Seq<int>, i: int, j: int)
    requires 0 <= i < j <= v.len()
    ensures sum(v, i, j-1) + v[j-1] == v[i] + sum(v, i+1, j)
    decreases j - i
{
    if i + 1 == j {
        // Base case: sum(v, i, i) + v[i] == v[i] + sum(v, i+1, i+1)
        // 0 + v[i] == v[i] + 0
    } else {
        lemma_sum_shift(v, i+1, j);
    }
}

proof fn lemma_sum_monotonic(v: Seq<int>, i: int, j: int, k: int)
    requires 0 <= i <= j <= k <= v.len()
    ensures sum(v, i, j) + sum(v, j, k) == sum(v, i, k)
    decreases k - j
{
    if j == k {
        // sum(v, i, j) + sum(v, j, j) == sum(v, i, j)
        // sum(v, i, j) + 0 == sum(v, i, j)
    } else {
        lemma_sum_monotonic(v, i, j, k-1);
        // sum(v, i, j) + sum(v, j, k-1) == sum(v, i, k-1)
        // sum(v, j, k) == sum(v, j, k-1) + v[k-1]
        // sum(v, i, k) == sum(v, i, k-1) + v[k-1]
    }
}

proof fn lemma_sum_max_to_right_helper(v: Seq<int>, i: int, max_sum: int, start: int)
    requires 0 <= start <= i < v.len()
    requires forall|l: int| start <= l <= i ==> sum(v, l, i+1) <= max_sum
    ensures sum_max_to_right2(v, start, i, max_sum)
{
    // This follows directly from the definition since sum2(v, l, i+1) == sum(v, l, i+1)
    assert forall|l: int, ss: int| start <= l <= i && ss == i + 1 ==> sum2(v, l, ss) <= max_sum by {
        lemma_sum_equivalence(v, l, ss);
    }
}

proof fn lemma_sum_extend_left(v: Seq<int>, i: int, j: int)
    requires 0 < i <= j <= v.len()
    ensures sum(v, i-1, j) == v[i-1] + sum(v, i, j)
{
    lemma_sum_monotonic(v, i-1, i, j);
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
    let mut current_sum = v[i] as i32;
    
    if i == 0 {
        return (max_sum, max_start);
    }
    
    let mut j = i;
    while j > 0
        invariant 
            j <= i < v.len(),
            max_start <= i,
            current_sum == sum(v@.map_values(|x: i32| x as int), j as int, (i+1) as int),
            max_sum == sum(v@.map_values(|x: i32| x as int), max_start as int, (i+1) as int),
            forall|l: int| j <= l <= i ==> sum(v@.map_values(|x: i32| x as int), l, (i+1) as int) <= max_sum,
    {
        j = j - 1;
        current_sum = current_sum + v[j];
        
        proof {
            let mapped_v = v@.map_values(|x: i32| x as int);
            lemma_sum_extend_left(mapped_v, (j+1) as int, (i+1) as int);
            assert(sum(mapped_v, j as int, (i+1) as int) == mapped_v[j as int] + sum(mapped_v, (j+1) as int, (i+1) as int));
            assert(current_sum == sum(mapped_v, j as int, (i+1) as int));
        }
        
        if current_sum > max_sum {
            max_sum = current_sum;
            max_start = j;
        }
    }
    
    proof {
        let mapped_v = v@.map_values(|x: i32| x as int);
        assert(forall|l: int| 0 <= l <= i ==> sum(mapped_v, l, (i+1) as int) <= max_sum);
    }
    
    (max_sum, max_start)
}
// </vc-code>

fn main() {
}

}