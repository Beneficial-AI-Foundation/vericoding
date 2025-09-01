use vstd::prelude::*;

verus! {

// <vc-helpers>
fn max_inclusive(arr: &[i32], lo: usize, hi: usize) -> i32
    requires
        arr.len() > 0,
        lo <= hi,
        hi < arr.len(),
    ensures
        forall |k: int| (lo as int) <= k && k <= (hi as int) ==> result >= arr@[k as usize],
    ensures
        exists |k: int| (lo as int) <= k && k <= (hi as int) && result == arr@[k as usize],
{
    let mut i: usize = lo + 1;
    let mut m: i32 = arr[lo];
    // invariants: i ranges and m is max over arr[lo..i-1]
    while i <= hi
        invariant lo + 1 <= i && i <= hi + 1
        invariant forall |k: int| (lo as int) <= k && k < (i as int) ==> m >= arr@[k as usize]
        invariant exists |k: int| (lo as int) <= k && k < (i as int) && m == arr@[k as usize]
    {
        let ai = arr[i];
        if ai > m {
            m = ai;
            // establish existential: i is witness
            proof {
                assert((i as int) >= (lo as int));
                assert((i as int) < (i as int) + 1); // trivial to satisfy range
            }
        }
        i = i + 1;
    }
    // now i == hi+1, so invariants give desired ensures
    m
}

fn min_inclusive(arr: &[i32], lo: usize, hi: usize) -> i32
    requires
        arr.len() > 0,
        lo <= hi,
        hi < arr.len(),
    ensures
        forall |k: int| (lo as int) <= k && k <= (hi as int) ==> result <= arr@[k as usize],
    ensures
        exists |k: int| (lo as int) <= k && k <= (hi as int) && result == arr@[k as usize],
{
    let mut i: usize = lo + 1;
    let mut m: i32 = arr[lo];
    // invariants: i ranges and m is min over arr[lo..i-1]
    while i <= hi
        invariant lo + 1 <= i && i <= hi + 1
        invariant forall |k: int| (lo as int) <= k && k < (i as int) ==> m <= arr@[k as usize]
        invariant exists |k: int| (lo as int) <= k && k < (i as int) && m == arr@[k as usize]
    {
        let ai = arr[i];
        if ai < m {
            m = ai;
            proof {
                assert((i as int) >= (lo as int));
            }
        }
        i = i + 1;
    }
    m
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn barrier(arr: &[i32], p: usize) -> (result: bool)
    // pre-conditions-start
    requires
        arr.len() > 0,
        0 <= p < arr.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        result == forall|k: int, l: int| 0 <= k <= p && p < l < arr.len() ==> arr[k] < arr[l],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    // handle trivial case where there is no element to the right of p
    if p + 1 >= arr.len() {
        // when there is no l with p < l < arr.len(), the universal condition is vacuously true
        return true;
    }

    let left_max = max_inclusive(arr, 0, p);
    let right_min = min_inclusive(arr, p + 1, arr.len() - 1);
    let res = left_max < right_min;

    // prove equivalence between res and the quantified property
    proof {
        // First direction: if left_max < right_min then for all k <= p < l, arr[k] < arr[l]
        if res {
            // left_max >= arr[k] for all k in [0..=p]
            assert(forall|k: int| 0 <= k && k <= (p as int) ==> left_max >= arr@[k as usize]);
            // right_min <= arr[l] for all l in [p+1..=arr.len()-1]
            assert(forall|l: int| ((p as int) + 1) <= l && l <= ((arr.len() - 1) as int) ==> right_min <= arr@[l as usize]);

            // combine to get arr[k] < arr[l]
            assert(forall|k: int, l: int|
                0 <= k && k <= (p as int) && (p as int) < l && l < (arr.len() as int) ==>
                    arr@[k as usize] < arr@[l as usize]
            );
        } else {
            // Second direction: if not res, show the quantified property is false
            // not res means left_max >= right_min
            // pick witnesses i,j where left_max == arr[i] and right_min == arr[j]
            assert(exists|i: int| 0 <= i && i <= (p as int) && left_max == arr@[i as usize]);
            assert(exists|j: int| ((p as int) + 1) <= j && j <= ((arr.len() - 1) as int) && right_min == arr@[j as usize]);

            // extract witnesses
            let (wi, wival): (int, i32) = proof {
                have H: exists|i: int| 0 <= i && i <= (p as int) && left_max == arr@[i as usize];
                let ex = H;
                ex
            };
            let (wj, wjval): (int, i32) = proof {
                have H2: exists|j: int| ((p as int) + 1) <= j && j <= ((arr.len() - 1) as int) && right_min == arr@[j as usize];
                let ex2 = H2;
                ex2
            };

            // Now left_max >= right_min implies arr[wi] >= arr[wj], violating the universal property
            assert(arr@[wi as usize] >= arr@[wj as usize]);
            // hence the universal property does not hold; establish negation of ensures is compatible
            // We can assert the universal property is false by providing these witnesses
            assert(! (forall|k: int, l: int|
                0 <= k && k <= (p as int) && (p as int) < l && l < (arr.len() as int) ==>
                    arr@[k as usize] < arr@[l as usize]
            ));
        }
    }

    res
    // impl-end
}
// </vc-code>

fn main() {}
}