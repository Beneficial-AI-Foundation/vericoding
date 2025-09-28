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
    let n: usize = v.len();
    let mut min_val: i32 = v[0];
    let mut i: usize = 1;
    while i < n
        invariant
            1 <= i <= n,
            min_val as int == min(v@.map_values(|x: i32| x as int), i as int)
        decreases (n - i) as nat
    {
        proof {
            assert(min_val as int == min(v@.map_values(|x: i32| x as int), i as int));
        }
        if v[i] < min_val {
            proof {
                assert(v[i] as int < min_val as int);
                // After update, min_val becomes v[i], which is the new minimum since v[i] < previous min
            }
            min_val = v[i];
        } else {
            proof {
                // min_val remains the same, and it's still the min of the first i+1 since v[i] >= min_val
            }
        }
        i += 1;
    }
    assert(min_val as int == min(v@.map_values(|x: i32| x as int), n as int));
    let mut c: i32 = 0;
    let mut j: usize = 0;
    while j < n
        invariant
            0 <= j <= n,
            c as int == count_min(v@.map_values(|x: i32| x as int), min_val as int, j as int)
        decreases (n - j) as nat
    {
        proof {
            assert(c as int == count_min(v@.map_values(|x: i32| x as int), min_val as int, j as int));
        }
        if v[j] == min_val {
            proof {
                assert(v[j] as int == min_val as int);
                // c will be incremented by 1, matching the spec
            }
            c += 1;
        }
        j += 1;
    }
    c
}
// </vc-code>

fn main() {
}

}