use vstd::prelude::*;

verus! {

spec fn min(v: Seq<int>, i: int) -> int
    decreases i
{
    if 1 <= i <= v.len() {
        if i == 1 {
            v[0]
        } else if v[i-1] <= min(v, i-1) {
            v[i-1]
        } else {
            min(v, i-1)
        }
    } else {
        0  // dummy value for invalid inputs
    }
}

proof fn min_property(v: Seq<int>, i: int)
    requires 1 <= i <= v.len()
    ensures forall|k: int| 0 <= k < i ==> v[k] >= min(v, i)
    decreases i
{
    if i > 1 {
        min_property(v, i-1);
    }
}

spec fn count_min(v: Seq<int>, x: int, i: int) -> int
    decreases i
{
    if 0 <= i <= v.len() {
        if i == 0 {
            0
        } else if v[i-1] == x {
            1 + count_min(v, x, i-1)
        } else {
            count_min(v, x, i-1)
        }
    } else {
        0  // dummy value for invalid inputs
    }
}

proof fn count_min_property(v: Seq<int>, x: int, i: int)
    requires 0 <= i <= v.len()
    ensures !(exists|k: int| 0 <= k < i && v[k] == x) ==> count_min(v, x, i) == 0
    decreases i
{
    if i > 0 {
        count_min_property(v, x, i-1);
    }
}

// <vc-helpers>
proof fn min_is_in_range(v: Seq<int>, i: int)
    requires 1 <= i <= v.len()
    ensures exists|k: int| 0 <= k < i && v[k] == min(v, i)
    decreases i
{
    if i == 1 {
        assert(v[0] == min(v, i));
    } else {
        min_is_in_range(v, i-1);
        if v[i-1] <= min(v, i-1) {
            assert(v[i-1] == min(v, i));
        } else {
            assert(min(v, i) == min(v, i-1));
        }
    }
}

proof fn count_min_monotonic(v: Seq<int>, x: int, i: int, j: int)
    requires 0 <= i <= j <= v.len()
    ensures count_min(v, x, i) <= count_min(v, x, j)
    decreases j - i
{
    if i < j {
        count_min_monotonic(v, x, i, j-1);
    }
}

proof fn count_min_positive(v: Seq<int>, x: int, i: int)
    requires 0 <= i <= v.len()
    requires exists|k: int| 0 <= k < i && v[k] == x
    ensures count_min(v, x, i) > 0
    decreases i
{
    if i > 0 {
        if v[i-1] == x {
        } else {
            count_min_positive(v, x, i-1);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn m_count_min(v: &Vec<i32>) -> (c: i32)
    requires v.len() > 0
    ensures c == count_min(v@.map_values(|x: i32| x as int), 
                          min(v@.map_values(|x: i32| x as int), v.len() as int), 
                          v.len() as int)
    //Implement and verify an O(v.len()) algorithm
// </vc-spec>
// <vc-code>
{
    let mut min_val = v[0];
    let mut i = 1;
    
    while i < v.len()
        invariant 
            0 < i <= v.len(),
            min_val == min(v@.map_values(|x: i32| x as int), i as int)
    {
        if v[i] < min_val {
            min_val = v[i];
        }
        i += 1;
    }
    
    let mut count = 0;
    let mut j = 0;
    
    while j < v.len()
        invariant 
            0 <= j <= v.len(),
            min_val == min(v@.map_values(|x: i32| x as int), v.len() as int),
            count == count_min(v@.map_values(|x: i32| x as int), min_val as int, j as int)
    {
        if v[j] == min_val {
            count += 1;
        }
        j += 1;
    }
    
    count
}
// </vc-code>

fn main() {
}

}