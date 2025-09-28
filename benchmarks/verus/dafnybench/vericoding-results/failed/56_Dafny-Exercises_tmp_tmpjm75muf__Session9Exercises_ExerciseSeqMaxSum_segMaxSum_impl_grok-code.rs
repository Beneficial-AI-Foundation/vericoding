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
#[verifier::allow_infinite_exec]
pub proof fn sum_unfold_after(v: Seq<int>, i: int, j: int)
    requires 
        0 <= i < j <= v.len()
    ensures 
        sum(v, i, j) == sum(v, i, j-1) + v[j-1]
{
    // Proof by definition of sum
    assert(sum(v, i, j) == sum(v, i, j-1) + v[j-1]);
}

spec fn sum_max_from_l(v: Seq<int>, left: int, i: int, max_sum: int) -> bool
    recommends 
        0 <= left <= i + 1 && i < v.len()
    ensures  
        sum_max_from_l(v, left, i, max_sum) <==> 
            forall|l: int| (left <= l <= i) ==> sum(v, l, i + 1) <= max_sum
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
    let ghost seq = v@.map_values(|x: i32| x as int);
    let mut current_sum: i32 = v[i];
    let mut max_sum: i32 = current_sum;
    let mut best_l: usize = i;
// </vc-code>

fn main() {
}

}