use vstd::prelude::*;

verus! {

spec fn min(a: int, b: int) -> int 
{
    if a < b { a } else { b }
}

spec fn min_function(a: int, b: int) -> int 
{
    if a < b { a } else { b }
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn min_array(a: &Vec<i32>) -> (m: i32)
    requires a.len() > 0
    ensures forall|k: int| 0 <= k < a.len() ==> m <= a[k]
    ensures exists|k: int| 0 <= k < a.len() && m == a[k]
// </vc-spec>
// <vc-code>
{
    let len = a.len();
    let mut i: usize = 1;
    let mut m: i32 = a[0];
    let mut best: usize = 0;

    proof {
        assert forall|k: int| 0 <= k && k < 1 ==> m <= #[trigger] a[k] {
            assert(k == 0);
        }
    }

    while i < len
        invariant
            1 <= (i as int) && (i as int) <= len
            && 0 <= (best as int) && (best as int) < (i as int)
            && m == a[best as int]
            && forall|k: int| 0 <= k && k < (i as int) ==> m <= #[trigger] a[k]
        decreases (len as int) - (i as int)
    {
        let old_m = m;
        let x = a[i];
        if x < m {
            m = x;
            best = i;
        }
        proof {
            assert forall|k: int| 0 <= k && k < (i as int) + 1 ==> m <= #[trigger] a[k] {
                if k < i as int {
                    assert(old_m <= a[k]);
                    if x < old_m {
                        assert(m == x);
                        assert(m < old_m);
                        assert(m <= old_m);
                    } else {
                        assert(m == old_m);
                        assert(m <= old_m);
                    }
                    assert(m <= a[k]);
                } else {
                    assert(k == i as int);
                    assert(a[i as int] == x);
                    if x < old_m {
                        assert(m == x);
                        assert(m <= a[i as int]);
                    } else {
                        assert(m == old_m);
                        assert(old_m <= x);
                        assert(m <= a[i as int]);
                    }
                }
            }
            if x < old_m {
                assert(best == i);
                assert(a[i as int] == x);
                assert(m == a[best as int]);
            } else {
                assert(m == old_m);
                assert(m == a[best as int]);
            }
        }
        i += 1;
    }

    m
}
// </vc-code>

fn main() {
}

}