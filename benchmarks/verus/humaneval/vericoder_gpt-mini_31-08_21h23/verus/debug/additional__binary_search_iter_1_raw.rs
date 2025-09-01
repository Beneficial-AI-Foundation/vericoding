```vc-helpers
// No helpers needed.
```

```vc-code
{
    // impl-start
    let mut l: usize = 0;
    let mut r: usize = arr.len();

    while l < r
        invariant
            l <= r,
            r <= arr.len(),
            forall|i: int| 0 <= i && i < l as int ==> arr[i as usize] != target,
            forall|i: int| r as int <= i && i < arr.len() as int ==> arr[i as usize] != target,
    {
        let mid: usize = l + (r - l) / 2;
        // mid is in [l, r)
        proof {
            assert(mid < r);
            assert(r <= arr.len());
            assert(mid < arr.len());
        }

        if arr[mid] == target {
            // Found it: return Some(mid)
            proof {
                // mid < arr.len() already established
                assert(arr[mid] == target);
                assert(arr.len() > 0);
            }
            return Some(mid);
        } else if arr[mid] < target {
            // Need to show new left invariant for l := mid + 1
            let old_l = l;
            proof {
                // show forall i < (mid+1): arr[i] != target
                assert(forall|i: int| 0 <= i && i < (mid as int) + 1 ==> arr[i as usize] != target by {
                    fix i;
                    assume(0 <= i && i < (mid as int) + 1);
                    if i < old_l as int {
                        // covered by old left invariant
                        assert(arr[i as usize] != target);
                    } else {
                        // old_l <= i <= mid
                        // if i == mid then arr[i] == arr[mid] < target
                        // if i < mid then arr[i] <= arr[mid] < target by monotonicity
                        if i == mid as int {
                            assert(arr[i as usize] == arr[mid]);
                            assert(arr[mid] < target);
                            assert(arr[i as usize] != target);
                        } else {
                            // i < mid
                            assert(0 <= i && i < mid as int && mid as int < arr.len() as int);
                            // from precondition: arr[i] <= arr[mid]
                            assert(arr[i as usize] <= arr[mid]);
                            assert(arr[mid] < target);
                            assert(arr[i as usize] != target);
                        }
                    }
                });
            }
            l = mid + 1;
        } else {
            // arr[mid] > target
            // Need to show new right invariant for r := mid
            let old_r = r;
            proof {
                // show forall i in [mid, old_r): arr[i] != target, so setting r := mid retains
                assert(forall|i: int| (mid as int) <= i && i < old_r as int ==> arr[i as usize] != target by {
                    fix i;
                    assume((mid as int) <= i && i < old_r as int);
                    // i in [mid, old_r)
                    // arr[i] >= arr[mid] > target, so arr[i] != target
                    if i == mid as int {
                        assert(arr[i as usize] == arr[mid]);
                        assert(arr[mid] > target);
                        assert(arr[i as usize] != target);
                    } else {
                        // i > mid
                        assert(mid as int < i && i < old_r as int && old_r as int <= arr.len() as int);
                        // from monotonicity arr[mid] <= arr[i]
                        assert(arr[mid] <= arr[i as usize]);
                        assert(arr[mid] > target);
                        assert(arr[i as usize] != target);
                    }
                });
            }
            r = mid;
        }
    }

    // Loop finished: l >= r
    proof {
        // From invariants: forall i < l arr[i] != target, forall i >= r arr[i] != target.
        // Since l >= r, every i in [0, arr.len()) is either < l or >= r.
        assert(forall|i: int| 0 <= i && i < arr.len() as int ==> arr[i as usize] != target by {
            fix i;
            assume(0 <= i && i < arr.len() as int);
            if i < l as int {
                assert(arr[i as usize] != target);
            } else {
                // i >= l >= r
                assert(i >= r as int);
                assert(arr[i as usize] != target);
            }
        });
    }

    None
    // impl-end
}
```