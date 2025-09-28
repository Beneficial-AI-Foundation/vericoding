// <vc-preamble>
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
        0
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
        0
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
// </vc-preamble>

// <vc-helpers>
fn compute_min(v: &Vec<i32>) -> (m: i32)
    requires
        v.len() > 0
    ensures
        m as int == min(v@.map_values(|x: i32| x as int), v.len() as int)
{
    let mut m = v[0];
    let mut i: usize = 1;
    while i < v.len()
        invariant
            v.len() > 0,
            1 <= i <= v.len(),
            m as int == min(v@.map_values(|x: i32| x as int), i as int)
        decreases v.len() - i
    {
        if v[i] <= m {
            m = v[i];
        }
        i = i + 1;
    }
    m
}

fn compute_count(v: &Vec<i32>, x: i32) -> (c: i32)
    ensures
        c as int == count_min(v@.map_values(|x: i32| x as int), x as int, v.len() as int)
{
    let mut c = 0;
    let mut i: usize = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            c as int == count_min(v@.map_values(|x: i32| x as int), x as int, i as int)
        decreases v.len() - i
    {
        if v[i] == x {
            c = c + 1;
        }
        i = i + 1;
    }
    c
}
// </vc-helpers>

// <vc-spec>
fn m_count_min(v: &Vec<i32>) -> (c: i32)
    requires v.len() > 0
    ensures c == count_min(v@.map_values(|x: i32| x as int), 
                          min(v@.map_values(|x: i32| x as int), v.len() as int), 
                          v.len() as int)
// </vc-spec>
// <vc-code>
{
    let min_val = compute_min(v);
    let count = compute_count(v, min_val);
    count
}
// </vc-code>

}
fn main() {}