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
proof fn min_property_lemma(v: Seq<int>, i: int, k: int)
    requires
        1 <= i <= v.len(),
        0 <= k < i,
    ensures v[k] >= min(v, i)
    decreases i
{
    min_property(v, i);
}

proof fn count_min_positive_lemma(v: Seq<int>, i: int)
    requires 
        1 <= i <= v.len(),
        exists|k: int| 0 <= k < i && v[k] == min(v, i),
    ensures count_min(v, min(v, i), i) > 0
    decreases i
{
    if i > 0 {
        if v[i-1] == min(v, i) {
            count_min_property(v, min(v, i), i-1);
        } else {
            count_min_positive_lemma(v, i-1);
        }
    }
}

proof fn min_eq_property(v: Seq<int>, i: int)
    requires 1 <= i <= v.len()
    ensures min(v, i) == min(v, i-1) || min(v, i) == v[i-1]
    decreases i
{
    if i > 1 {
        min_eq_property(v, i-1);
    }
}

proof fn ghost_map_values_preserves_properties(v: &Vec<i32>) -> (ghost_v: Seq<int>)
    ensures
        ghost_v == v@.map_values(|x: i32| x as int),
        ghost_v.len() == v.len(),
        forall|i: int| 0 <= i < v.len() ==> ghost_v[i] == v[i] as int
{
    v@.map_values(|x: i32| x as int)
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
    let ghost_v = proof { ghost_map_values_preserves_properties(v) };
    
    let mut min_val = v[0];
    let mut count = 1;
    
    let mut i: usize = 1;
    while i < n
        invariant
            i <= n,
            forall|k: int| 0 <= k < i as int ==> ghost_v[k] >= (min_val as int),
            exists|k: int| 0 <= k < i as int && ghost_v[k] == (min_val as int),
            count == count_min(ghost_v, min_val as int, i as int),
        decreases n - i
    {
        let current_val = v[i];
        if current_val < min_val {
            min_val = current_val;
            count = 1;
        } else if current_val == min_val {
            count += 1;
        }
        
        proof {
            let i_int = i as int;
            if current_val < min_val {
                assert(forall|k: int| 0 <= k <= i_int ==> ghost_v[k] >= (current_val as int));
                assert(ghost_v[i_int] == (current_val as int));
            } else if current_val == min_val {
                assert(forall|k: int| 0 <= k < i_int ==> ghost_v[k] >= (min_val as int));
                assert(ghost_v[i_int] == (min_val as int));
            } else {
                assert(forall|k: int| 0 <= k <= i_int ==> ghost_v[k] >= (min_val as int));
                assert(ghost_v[i_int] > (min_val as int));
            }
        }
        
        i += 1;
    }
    
    count
}
// </vc-code>

fn main() {
}

}