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
proof fn min_property_alt(v: Seq<int>, i: int)
    requires 0 <= i <= v.len()
    ensures forall|k: int| 0 <= k < i ==> v[k] >= min(v, i)
    decreases i
{
    if i > 0 {
        if i == 1 {
            // Base case: i = 1
        } else {
            min_property_alt(v, i-1);
            if v[i-1] <= min(v, i-1) {
                // v[i-1] is the new min candidate
                assert(min(v,i) == v[i-1]);
                assert(forall|k: int| 0 <= k < i - 1 ==> v[k] >= min(v, i-1));
                // We need to show v[k] >= v[i-1] for 0 <= k < i-1
                // and v[i-1] >= v[i-1] obviously holds.
                // From min(v,i-1) property, we have v[k] >= min(v,i-1).
                // If v[i-1] is new min, then v[i-1] <= min(v,i-1).
                // So v[k] >= min(v,i-1) >= v[i-1]. Thus v[k] >= v[i-1].
            } else {
                // min(v,i-1) is still the min
                assert(min(v,i) == min(v,i-1));
                assert(forall|k: int| 0 <= k < i - 1 ==> v[k] >= min(v, i-1));
                // And v[i-1] >= min(v,i-1) is given by the `else if` condition.
            }
        }
    }
}

proof fn min_value_is_in_range(v: Seq<int>, i: int)
    requires 1 <= i <= v.len()
    ensures exists|k: int| 0 <= k < i && #[trigger] v[k] == min(v, i)
    decreases i
{
    if i == 1 {
        assert(min(v,1) == v[0]);
    } else {
        if v[i-1] <= min(v, i-1) {
            assert(min(v,i) == v[i-1]);
            // This case proves that v[i-1] is the minimum, which is within the range [0, i-1].
        } else {
            assert(min(v,i) == min(v,i-1));
            min_value_is_in_range(v, i-1);
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
    let mut current_min: i32 = v[0];
    let mut min_count: i32 = 0;

    if v.len() == 0 {
        return 0; // Should not happen due to precondition v.len() > 0
    }

    // First pass to find the minimum value
    let mut i: int = 1;
    while i < v.len() as int
        invariant 1 <= i <= v.len() as int,
        invariant current_min as int == min(v@.map_values(|x: i32| x as int), i),
        invariant forall|k: int| 0 <= k < i ==> (v@.map_values(|x: i32| x as int))@[k] >= current_min as int,
        invariant {
            min_value_is_in_range(v@.map_values(|x:i32| x as int), i); true
        }
    {
        let val_i = v[i as usize];
        if val_i < current_min {
            current_min = val_i;
        }
        i = i + 1;
    }
    // After the loop, current_min is the overall minimum
    assert(current_min as int == min(v@.map_values(|x: i32| x as int), v.len() as int));
    min_property_alt(v@.map_values(|x: i32| x as int), v.len() as int);


    // Second pass to count occurrences of the minimum value
    let mut j: int = 0;
    while j < v.len() as int
        invariant 0 <= j <= v.len() as int,
        invariant min_count as int == count_min(v@.map_values(|x: i32| x as int),
                                                current_min as int,
                                                j)
    {
        if v[j as usize] == current_min {
            min_count = min_count + 1;
        }
        j = j + 1;
    }

    min_count
}
// </vc-code>

fn main() {
}

}