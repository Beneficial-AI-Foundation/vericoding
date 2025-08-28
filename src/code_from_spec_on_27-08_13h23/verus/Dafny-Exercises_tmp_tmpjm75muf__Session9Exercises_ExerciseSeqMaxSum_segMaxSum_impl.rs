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
proof fn sum_equals_sum2(v: Seq<int>, i: int, j: int)
    requires 0 <= i <= j <= v.len()
    ensures sum(v, i, j) == sum2(v, i, j)
    decreases j - i
{
    if i == j {
        assert(sum(v, i, j) == 0);
        assert(sum2(v, i, j) == 0);
    } else {
        sum_equals_sum2(v, i, j - 1);
        assert(sum(v, i, j) == sum(v, i, j - 1) + v[j - 1]);
        assert(sum2(v, i, j) == v[i] + sum2(v, i + 1, j));
        reveal_with_fuel(sum2, 2);
    }
}

proof fn sum_max_to_right_implies_sum_max_to_right2(v: Seq<int>, i: int, s: int)
    requires 0 <= i < v.len(), sum_max_to_right(v, i, s)
    ensures sum_max_to_right2(v, 0, i, s)
{
    assert forall|l: int, ss: int| 0 <= l <= i && ss == i + 1 implies sum2(v, l, ss) <= s by {
        sum_equals_sum2(v, l, ss);
        assert(sum(v, l, ss) <= s);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn seg_max_sum(v: &[i32], i: usize) -> (i32, usize)
    requires v.len() > 0 && i < v.len()
    ensures |result: (i32, usize)|
        result.1 <= i && 
        result.0 == sum(v@.map_values(|x: i32| x as int), result.1 as int, (i+1) as int) &&
        sum_max_to_right(v@.map_values(|x: i32| x as int), i as int, result.0 as int)
// </vc-spec>
// </vc-spec>

// <vc-code>
fn seg_max_sum(v: &[i32], i: usize) -> (i32, usize)
    requires v.len() > 0 && i < v.len()
    ensures |result: (i32, usize)|
        result.1 <= i && 
        result.0 == sum(v@.map_values(|x: i32| x as int), result.1 as int, (i+1) as int) &&
        sum_max_to_right(v@.map_values(|x: i32| x as int), i as int, result.0 as int)
{
    let mut max_sum: i32 = v[i];
    let mut max_start: usize = i;
    let mut current_sum: i32 = v[i];
    let mut start: usize = i;
    
    while start > 0
        invariant
            0 <= start <= i,
            max_start <= i,
            current_sum == sum(v@.map_values(|x: i32| x as int), start as int, (i+1) as int),
            max_sum == sum(v@.map_values(|x: i32| x as int), max_start as int, (i+1) as int),
            sum_max_to_right(v@.map_values(|x: i32| x as int), i as int, max_sum as int)
    {
        start = start - 1;
        current_sum = current_sum + v[start];
        
        if current_sum > max_sum {
            max_sum = current_sum;
            max_start = start;
        }
    }
    
    (max_sum, max_start)
}
// </vc-code>

fn main() {
}

}