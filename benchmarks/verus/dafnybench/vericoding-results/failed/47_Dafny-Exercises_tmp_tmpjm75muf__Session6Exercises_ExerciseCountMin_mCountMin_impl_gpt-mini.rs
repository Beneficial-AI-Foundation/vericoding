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
proof fn vec_index_to_spec(v: &Vec<i32>, i: int)
    requires 0 <= i && i < v.len() as int
    ensures v@.map_values(|x: i32| x as int)@[i] == (v[i as usize] as int)
{
    let s = v@.map_values(|x: i32| x as int);
    assert(s@[i] == v[i as usize] as int);
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
    let s = v@.map_values(|x: i32| x as int);
    let n: usize = v.len();
    // n > 0 by precondition
    let mut i: usize = 1usize;
    let mut curr_min: i32 = v[0];
    let mut cnt: i32 = 1;

    proof {
        // establish initial invariants for i = 1
        vec_index_to_spec(v, 0);
        assert(s@[0] == v[0] as int);
        assert((curr_min as int) == min(s, 1));
        assert((cnt as int) == count_min(s, curr_min as int, 1));
    }

    while i < n
        invariant 1usize <= i && i <= n;
        invariant n >= 1usize;
        invariant (curr_min as int) == min(s, i as int);
        invariant (cnt as int) == count_min(s, curr_min as int, i as int);
        decreases (n - i);
    {
        let prev_min_int = curr_min as int;
        let prev_cnt_int = cnt as int;
        // get current element
        let a: i32 = v[i];
        let a_int: int = a as int;
        proof {
            // relate runtime index to spec sequence
            vec_index_to_spec(v, i as int);
            assert(s@[i as int] == a_int);
            // invariants give previous relations
            assert(prev_min_int == min(s, i as int));
            assert(prev_cnt_int == count_min(s, prev_min_int, i as int));
        }

        if a_int < prev_min_int {
            // new minimum found
            curr_min = a;
            cnt = 1;
            proof {
                // s@[i] == a_int
                assert(s@[i as int] == a_int);
                // prev_min_int == min(s,i)
                assert(prev_min_int == min(s, i as int));
                // from a_int < prev_min_int and min_property, no earlier element equals a_int
                min_property(s, i as int);
                assert(prev_min_int > a_int);
                // from min_property: forall k < i, s@[k] >= prev_min_int > a_int
                assert(!(exists|k: int| 0 <= k && k < i as int && s@[k] == a_int));
                // thus count_min on first i elements for a_int is 0
                count_min_property(s, a_int, i as int);
                assert(count_min(s, a_int, i as int) == 0);
                // therefore count_min for i+1 equals 1
                assert(count_min(s, a_int, i as int + 1) == 1);
                // min for i+1 equals a_int
                assert(min(s, i as int + 1) == a_int);
                assert((curr_min as int) == min(s, i as int + 1));
                assert((cnt as int) == count_min(s, curr_min as int, i as int + 1));
            }
        } else {
            if a_int == prev_min_int {
                cnt = cnt + 1;
                proof {
                    // min stays the same
                    assert(min(s, i as int + 1) == prev_min_int);
                    // count_min increases by 1 because last element equals x
                    assert(count_min(s, prev_min_int, i as int + 1) ==
                           1 + count_min(s, prev_min_int, i as int));
                    assert((cnt as int) == count_min(s, curr_min as int, i as int + 1));
                    assert((curr_min as int) == min(s, i as int + 1));
                }
            } else {
                // a_int > prev_min_int: nothing changes except extending prefix
                proof {
                    assert(min(s, i as int + 1) == prev_min_int);
                    assert(count_min(s, prev_min_int, i as int + 1) ==
                           count_min(s, prev_min_int, i as int));
                    assert((curr_min as int) == min(s, i as int + 1));
                    assert((cnt as int) == count_min(s, curr_min as int, i as int + 1));
                }
            }
        }

        i = i + 1;
    }

    // At loop exit i == n, invariants give the desired result
    proof {
        assert((cnt as int) == count_min(s, curr_min as int, n as int));
        assert((curr_min as int) == min(s, n as int));
    }

    cnt
}
// </vc-code>

fn main() {
}

}