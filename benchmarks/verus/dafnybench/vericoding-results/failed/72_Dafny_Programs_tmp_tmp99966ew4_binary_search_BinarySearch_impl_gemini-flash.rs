use vstd::prelude::*;

verus! {

spec fn sorted(a: &[int]) -> bool {
    forall|j: int, k: int| 0 <= j < k < a.len() ==> a[j] <= a[k]
}

// <vc-helpers>
fn value_not_found(a: &[int], value: int, low: int, high: int) -> (b: bool)
    requires
        low > high,
        low as nat <= a.len(),
        high as int >= -1,
        // The helper function needs to reflect the invariant conditions as well as the termination condition
        // from the `binary_search` function's loop.
        forall|k: int| 0 <= k < low ==> #[trigger] (a[k] != value),
        forall|k: int| high < k < a.len() ==> #[trigger] (a[k] != value),
        sorted(a)
    ensures
        forall|k: int| 0 <= k < a.len() ==> a[k] != value,
{
    // Proof of value_not_found
    proof {
        // We know from the loop invariants that:
        // 1. All elements from 0 to low-1 are not `value`.
        // 2. All elements from high+1 to a.len()-1 are not `value`.
        // Since low > high, the ranges [0, low-1] and [high+1, a.len()-1]
        // cover the entire array [0, a.len()-1].
        // Specifically, for any k in [0, a.len()-1]:
        // If k < low, then a[k] != value.
        // If k > high, then a[k] != value.
        // Since low > high, there are no k such that low <= k <= high.
        // Therefore, for all k in [0, a.len()-1], a[k] != value.

        assert(low > high);
        assert(low as nat <= a.len());
        assert(high as int >= -1);
        assert(forall|k: int| 0 <= k < low ==> #[trigger] (a[k] != value));
        assert(forall|k: int| high < k < a.len() ==> #[trigger] (a[k] != value));

        assert(forall|k: int| 0 <= k < a.len() implies a[k] != value) by {
            assert forall|k: int| 0 <= k < a.len() implies a[k] != value by {
                if k < low {
                    assert(a[k] != value);
                } else if k > high {
                    assert(a[k] != value);
                } else {
                    // This case is impossible because low > high.
                    // If low <= k <= high were possible, it would contradict low > high.
                    // Therefore, no such k exists in the loop's context when low > high.
                }
            }
        };
    }
    true
}
// </vc-helpers>

// <vc-spec>
fn binary_search(a: &[int], value: int) -> (index: i32)
    requires 
        sorted(a),
    ensures 
        0 <= index ==> index < a.len() && a[index as int] == value,
        index < 0 ==> forall|k: int| 0 <= k < a.len() ==> a[k] != value,
// </vc-spec>
// <vc-code>
{
    let mut low: nat = 0;
    let mut high: int = a.len() as int - 1;

    while low as int <= high
        invariant
            0 <= low as int,
            high < a.len() as int || high == -1,
            low as nat <= a.len(),
            high >= -1,
            forall|k: int| 0 <= k < low as int ==> #[trigger] (a[k] != value),
            forall|k: int| high < k < a.len() ==> #[trigger] (a[k] != value),
            sorted(a),
    {
        if a.len() == 0 {
            break;
        }

        let mid_int: int = low as int + (high - low as int) / 2;
        let mid: nat = mid_int as nat;

        assert(0 <= mid_int && mid_int < a.len());

        if a[mid as int] == value {
            return mid as i32;
        } else if a[mid as int] < value {
            low = (mid_int + 1) as nat;
        } else {
            high = mid_int - 1;
        }
    }

    if low as int > high {
        // Call the helper function to prove that the value is not in the array
        value_not_found(a, value, low as int, high);
    }

    -1
}
// </vc-code>

fn main() {
}

}