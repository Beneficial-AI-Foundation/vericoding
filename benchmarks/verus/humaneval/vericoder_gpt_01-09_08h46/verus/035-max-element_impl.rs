use vstd::prelude::*;

verus! {

// <vc-helpers>
// no additional helpers needed
// </vc-helpers>

// <vc-spec>
fn max_element(a: &Vec<i32>) -> (max: i32)
    // pre-conditions-start
    requires
        a.len() > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|i: int| 0 <= i < a.len() ==> a[i] <= max,
        exists|i: int| 0 <= i < a.len() && a[i] == max,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    let mut i: usize = 1;
    let mut idx: usize = 0;

    while i < n
        invariant
            1 <= i as int && i as int <= n as int,
            0 <= idx as int && idx as int < i as int,
            forall|j: int| 0 <= j && j < (i as int) ==> #[trigger] a[j] <= a[idx as int],
        decreases (n as int) - (i as int)
    {
        let old_idx = idx;
        let ai = a[i];
        let gt = ai > a[old_idx];
        if gt {
            idx = i;
        }

        assert forall|j:int| 0 <= j && j < ((i + 1) as int) ==> #[trigger] a[j] <= a[idx as int] by {
            if j < (i as int) {
                assert(a[j] <= a[old_idx as int]);
                if gt {
                    assert(a[old_idx as int] < ai);
                    assert(a[j] <= ai);
                } else {
                    assert(a[j] <= a[idx as int]);
                }
            } else {
                assert(j == (i as int));
                if gt {
                    assert(a[j] == a[idx as int]);
                    assert(a[j] <= a[idx as int]);
                } else {
                    assert(ai <= a[old_idx as int]);
                    assert(a[j] <= a[idx as int]);
                }
            }
        };

        assert(0 <= idx as int && idx as int < ((i + 1) as int)) by {
            if gt {
                assert(idx as int == i as int);
                assert(i as int < (i + 1) as int);
            } else {
                assert(idx as int == old_idx as int);
                assert(old_idx as int < i as int);
                assert(i as int < (i + 1) as int);
                assert(old_idx as int < (i + 1) as int);
            }
        };

        i = i + 1;
    }

    assert(i as int == n as int);
    assert(0 <= idx as int && idx as int < n as int);

    assert forall|j:int| 0 <= j && j < (n as int) ==> #[trigger] a[j] <= a[idx as int] by {
        assert(i as int == n as int);
        assert(0 <= j && j < i as int);
    };

    let max = a[idx];

    proof {
        assert(exists|k:int| 0 <= k && k < (a.len() as int) && a[k] == max) by {
            let k = idx as int;
            assert(0 <= k && k < (a.len() as int)) by {
                assert(a.len() as int == n as int);
                assert(0 <= idx as int && idx as int < n as int);
            }
            assert(a[k] == max);
        }
    }

    max
}
// </vc-code>

fn main() {}
}