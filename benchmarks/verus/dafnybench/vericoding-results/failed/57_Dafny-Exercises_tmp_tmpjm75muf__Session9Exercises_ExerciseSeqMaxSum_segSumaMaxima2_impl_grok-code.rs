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
// No additional helpers needed for this implementation

proof fn sum2_closed(v: Seq<i32>, i: int, j: int) -> int
    requires 0 <= i <= j <= v.len()
    decreases j - i when i < j
{
    if i == j {
        0
    } else {
        v[i] as int + sum2_closed(v, i + 1, j)
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
    let mut j = i;
    let mut current_sum = v[i];
    let mut max_sum = v[i];
    let mut best_start = i;
    while j > 0
        invariant
            j <= i,
            j >= 0,
            current_sum as int == sum2(v@, j as int, ((i as int) + 1) as int),
            forall |k: int| #[trigger] (j <= k && k <= i) ==> sum2(v@, k as int, ((i as int) + 1) as int) <= max_sum as int,
            sum2(v@, best_start as int, ((i as int) + 1) as int) == max_sum as int,
            best_start <= i,
        decreases j
    {
        j = j - 1;
        current_sum = v[j] + current_sum;
        if current_sum > max_sum {
            max_sum = current_sum;
            best_start = j;
        }
        proof {
            assert(current_sum as int == sum2(v@, j as int, ((i as int) + 1) as int));
            assert(forall |k: int| j <= k && k <= i ==> sum2(v@, k as int, ((i as int) + 1) as int) <= max_sum as int);
        }
    }
    (max_sum, best_start)
}
// </vc-code>

fn main() {}

}