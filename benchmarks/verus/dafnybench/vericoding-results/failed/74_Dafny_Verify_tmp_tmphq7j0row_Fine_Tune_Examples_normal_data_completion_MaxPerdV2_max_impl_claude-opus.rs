use vstd::prelude::*;

verus! {

spec fn contains(v: i32, a: Seq<i32>, n: int) -> bool {
    exists|j: int| 0 <= j < n && a[j] == v
}

spec fn upper_bound(v: i32, a: Seq<i32>, n: int) -> bool {
    forall|j: int| 0 <= j < n ==> a[j] <= v
}

spec fn is_max(m: i32, a: Seq<i32>, n: int) -> bool {
    contains(m, a, n) && upper_bound(m, a, n)
}

// <vc-helpers>
// No additional helpers needed
// </vc-helpers>

// <vc-spec>
fn max(a: &[i32], n: usize) -> (max: i32)
    requires 0 < n <= a.len(),
    ensures is_max(max, a@, n as int),
// </vc-spec>
// <vc-code>
{
    let mut max_val = a[0];
    let mut i: usize = 1;
    
    while i < n
        invariant
            0 < i <= n,
            n <= a.len(),
            is_max(max_val, a@, i as int),
    {
        let old_max = max_val;
        if a[i as int] > max_val {
            max_val = a[i as int];
        }
        
        assert(contains(max_val, a@, (i + 1) as int)) by {
            if a[i as int] > old_max {
                assert(a@[i as int] == max_val);
            } else {
                assert(max_val == old_max);
                assert(contains(old_max, a@, i as int));
            }
        }
        
        assert(upper_bound(max_val, a@, (i + 1) as int)) by {
            assert forall|j: int| 0 <= j < (i + 1) as int implies a@[j] <= max_val by {
                if j < i as int {
                    assert(upper_bound(old_max, a@, i as int));
                    assert(a@[j] <= old_max);
                    assert(old_max <= max_val);
                    assert(a@[j] <= max_val);
                } else {
                    assert(j == i as int);
                    assert(a@[j] == a[i as int]);
                    if a[i as int] > old_max {
                        assert(max_val == a[i as int]);
                        assert(a@[j] == max_val);
                        assert(a@[j] <= max_val);
                    } else {
                        assert(max_val == old_max);
                        assert(a@[j] <= max_val);
                    }
                }
            }
        }
        
        i = i + 1;
    }
    
    max_val
}
// </vc-code>

fn main() {}

}