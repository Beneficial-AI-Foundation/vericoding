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
proof fn min_is_element(v: Seq<int>, i: int)
    requires 1 <= i <= v.len()
    ensures exists|k: int| 0 <= k < i && v[k] == min(v, i)
    decreases i
{
    if i == 1 {
        assert(v[0] == min(v, 1));
    } else {
        if v[i-1] <= min(v, i-1) {
            assert(v[i-1] == min(v, i));
        } else {
            min_is_element(v, i-1);
        }
    }
}

proof fn count_min_bounds(v: Seq<int>, x: int, i: int)
    requires 0 <= i <= v.len()
    ensures count_min(v, x, i) >= 0
    decreases i
{
    if i > 0 {
        count_min_bounds(v, x, i-1);
    }
}

proof fn min_step(v: Seq<int>, i: int, m: int)
    requires 1 <= i < v.len()
    requires m == min(v, i)
    ensures min(v, i+1) == if v[i] <= m { v[i] } else { m }
{
    assert(i + 1 <= v.len());
    if v[i] <= min(v, i) {
        assert(min(v, i+1) == v[i]);
    } else {
        assert(min(v, i+1) == min(v, i));
    }
}

proof fn count_step(v: Seq<int>, x: int, i: int, c: int)
    requires 0 <= i < v.len()
    requires c == count_min(v, x, i)
    ensures count_min(v, x, i+1) == if v[i] == x { c + 1 } else { c }
{
    assert(i + 1 <= v.len());
    if v[i] == x {
        assert(count_min(v, x, i+1) == 1 + count_min(v, x, i));
        assert(count_min(v, x, i+1) == c + 1);
    } else {
        assert(count_min(v, x, i+1) == count_min(v, x, i));
        assert(count_min(v, x, i+1) == c);
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
    let v_seq = v@.map_values(|x: i32| x as int);
    
    // First pass: find the minimum
    let mut min_val = v[0];
    let mut i: usize = 1;
    
    while i < v.len()
        invariant 1 <= i <= v.len()
        invariant min_val as int == min(v_seq, i as int)
    {
        proof {
            min_step(v_seq, i as int, min_val as int);
        }
        
        if v[i] < min_val {
            min_val = v[i];
        }
        i = i + 1;
    }
    
    assert(min_val as int == min(v_seq, v.len() as int));
    
    // Second pass: count occurrences of minimum
    let mut count: i32 = 0;
    let mut j: usize = 0;
    
    while j < v.len()
        invariant 0 <= j <= v.len()
        invariant count as int == count_min(v_seq, min_val as int, j as int)
    {
        proof {
            count_step(v_seq, min_val as int, j as int, count as int);
        }
        
        if v[j] == min_val {
            count = count + 1;
        }
        j = j + 1;
    }
    
    count
}
// </vc-code>

fn main() {
}

}