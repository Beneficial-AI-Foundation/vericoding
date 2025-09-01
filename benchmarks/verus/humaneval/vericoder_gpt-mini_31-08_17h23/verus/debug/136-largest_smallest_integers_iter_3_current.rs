use vstd::prelude::*;

verus! {

// <vc-helpers>
// <vc-helpers>
// No helper lemmas needed for this proof.
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn largest_smallest_integers(arr: &Vec<i32>) -> (res: (Option<i32>, Option<i32>))
    // post-conditions-start
    ensures
        ({
            let a = res.0;
            let b = res.1;
            &&& a.is_none() ==> forall|i: int| 0 <= i < arr@.len() ==> arr@[i] >= 0
            &&& a.is_some() ==> arr@.contains(a.unwrap()) && a.unwrap() < 0
            &&& a.is_some() ==> forall|i: int|
                0 <= i < arr@.len() && arr@[i] < 0 ==> arr@[i] <= a.unwrap()
            &&& b.is_none() ==> forall|i: int| 0 <= i < arr@.len() ==> arr@[i] <= 0
            &&& b.is_some() ==> arr@.contains(b.unwrap()) && b.unwrap() > 0
            &&& b.is_some() ==> forall|i: int|
                0 <= i < arr@.len() && arr@[i] > 0 ==> arr@[i] >= b.unwrap()
        }),
    // post-conditions-end
// </vc-spec>
// <vc-code>
// <vc-code>
{
    // impl-start
    let mut i: int = 0;
    let n: int = arr@.len();
    let mut neg: Option<i32> = None;
    let mut pos: Option<i32> = None;

    while i < n
        invariant 0 <= i && i <= n;
        invariant (neg.is_none() ==> forall|k: int| 0 <= k < i ==> arr@[k] >= 0);
        invariant (neg.is_some() ==> exists|k: int| 0 <= k < i && arr@[k] == neg.unwrap() && neg.unwrap() < 0);
        invariant (neg.is_some() ==> forall|k: int| 0 <= k < i && arr@[k] < 0 ==> arr@[k] <= neg.unwrap());
        invariant (pos.is_none() ==> forall|k: int| 0 <= k < i ==> arr@[k] <= 0);
        invariant (pos.is_some() ==> exists|k: int| 0 <= k < i && arr@[k] == pos.unwrap() && pos.unwrap() > 0);
        invariant (pos.is_some() ==> forall|k: int| 0 <= k < i && arr@[k] > 0 ==> arr@[k] >= pos.unwrap());
        decreases n - i;
    {
        let v: i32 = arr[i as usize];
        proof {
            assert(0 <= i && i < n);
            assert(arr@[i] == v);
        }

        if v < 0 {
            match neg {
                None => {
                    // set first negative seen
                    neg = Some(v);
                    proof {
                        // now there exists k < i+1 with arr@[k] == neg.unwrap()
                        assert(neg.is_some());
                        assert(arr@[i] == neg.unwrap());
                    }
                }
                Some(old) => {
                    if v > old {
                        neg = Some(v);
                        proof {
                            assert(neg.is_some());
                            assert(arr@[i] == neg.unwrap());
                        }
                    } else {
                        // keep old; nothing to prove here
                    }
                }
            }
        }

        if v > 0 {
            match pos {
                None => {
                    pos = Some(v);
                    proof {
                        assert(pos.is_some());
                        assert(arr@[i] == pos.unwrap());
                    }
                }
                Some(old) => {
                    if v < old {
                        pos = Some(v);
                        proof {
                            assert(pos.is_some());
                            assert(arr@[i] == pos.unwrap());
                        }
                    } else {
                        // keep old
                    }
                }
            }
        }

        i = i + 1;
    }

    // At loop exit we have invariants across full array
    (neg, pos)
    // impl-end
}
// </vc-code>
// </vc-code>

fn main() {}
}