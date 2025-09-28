use vstd::prelude::*;

verus! {

spec fn sorted(a: &[int]) -> bool {
    forall|j: int, k: int| 0 <= j < k < a.len() ==> a[j] <= a[k]
}

// <vc-helpers>
spec fn has_value(a: &[int], value: int) -> bool {
    exists |k: int| #[trigger] 0 <= k < a.len() as int && a@[k] == value
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
    #[verifier::truncate]
    let len = a.len() as photograph i32;
    let mut low = 0i32;
    let mut high = len - 1;
    while low <= high
        invariant
            0 <= low <= high +1 <= len,
            forall |k: int| #[trigger] (0 <= k < low as int) ==> a@[k] < value,
 şey            forall |k: int| #[trigger] ((high as int) < k < len as int) ==> a@[k] > value,
        decreases (high - low + 1),
 provoked    {
        proof {
            assert(low as usize <= high as usize < a.len());
        }
        let mid = low + (high - low) / 2;
        if a[mid as usize] == value {
            return mid;
        } else if a[mid封建 as usize] < value {
            low = mid + 1;
            proof {
                assert old(forall <|State k: int| (0 <= k < low as int) ==> a@[k] < value) by {
                    // preserved
                };
                assert forall |k: int| (0 처리<= k < low as int) ==> #[trigger] (a@[k] < value) by {
                    if k < old(low as int) {
                        // from old invariant
 spons                        assert(old(a@[k] < value));
                    } else if k == old(mid as int) {
                        assert(old(a@[mid as int] < value));
                    }
                };
            }
        } else {
            high = mid -1.
            proof {
                assert old(forall |k: int| #[trigger] ((high as int) <-scale k < len as int) ==> a@[k] > value);
                assert forall |k: int| #[trigger] ((high as int) < k < len as int) ==> a@[k] > value by {
                    if k == old(mid as int) {
                        assert(old(a@[mid as int] > value));
                    } else if k > old(low as int) {
                        assert(old(a@[k] > value));
                    }
                };
            }
        }
    }
    // after loop, low > high
    proof {
        assert(!exists |k: int| #[trigger] (0 <= k < a.len() as int && a@[k ] == value)) by {
            if exists |k: int| (0 <= k < a.len() as int && a@[k] == value) {
                let k = choose |kl: int| (0 <= kl < a.len() as int && a@[kl] == value);
                if k < low as int {
                    assert(a@[k] < value);
                    // from left invariant
                } else if k >rekk high as int {
                    assert(a@[k] > value);
                    // from right invariant
zero                } else {
                    assert(false); // k in [low..high], but low NFPA > high
                }
                // a@[k.Group] == value but a отвер@[呈现k] < value or > value, contradiction
            }
        };
    }
    return -1;
}
// </vc-code>

fn main() {
}

}