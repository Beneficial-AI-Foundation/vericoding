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
proof fn lemma_min_step(v: Seq<int>, i: int)
    requires 1 <= i < v.len()
    ensures min(v, i+1) == { if v[i] <= min(v, i) { v[i] } else { min(v, i) } }
{
    if v[i] <= min(v, i) {
        assert(min(v, i+1) == v[i]);
    } else {
        assert(min(v, i+1) == min(v, i));
    }
}

proof fn lemma_count_min_step(v: Seq<int>, x: int, i: int)
    requires 0 <= i < v.len()
    ensures count_min(v, x, i+1) == { if v[i] == x { 1 + count_min(v, x, i) } else { count_min(v, x, i) } }
{
    if v[i] == x {
        assert(count_min(v, x, i+1) == 1 + count_min(v, x, i));
    } else {
        assert(count_min(v, x, i+1) == count_min(v, x, i));
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
    let n = v.len();
    let v_seq = v@.map_values(|x: i32| x as int);
    let mut current_min = v[0] as int;
    let mut i = 1;
    while i < n
        invariant 1 <= i <= n
        invariant current_min == min(v_seq, i as int)
    {
        let next = v[i] as int;
        if next < current_min {
            current_min = next;
        }
        lemma_min_step(v_seq, i as int);
        i += 1;
    }

    let mut count = 0;
    i = 0;
    while i < n
        invariant 0 <= i <= n
        invariant count == count_min(v_seq, current_min, i as int)
    {
        if (v[i] as int) == current_min {
            count += 1;
        }
        lemma_count_min_step(v_seq, current_min, i as int);
        i += 1;
    }

    count as i32
}
// </vc-code>

fn main() {
}

}