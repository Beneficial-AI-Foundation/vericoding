use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn find_even_numbers(arr: &[i32]) -> (even_numbers: Vec<i32>)
    ensures 
        (forall|x: i32| arr@.contains(x) && x % 2 == 0 ==> even_numbers@.contains(x)) &&
        (forall|x: i32| !arr@.contains(x) ==> !even_numbers@.contains(x)) &&
        (forall|k: int| 0 <= k < even_numbers@.len() ==> even_numbers@[k] % 2 == 0) &&
        (forall|k: int, l: int| 0 <= k < l < even_numbers@.len() ==> 
            exists|n: int, m: int| 0 <= n < m < arr@.len() && 
            #[trigger] even_numbers@[k] == #[trigger] arr@[n] && 
            #[trigger] even_numbers@[l] == #[trigger] arr@[m])
// </vc-spec>
// <vc-code>
{
    let mut res: Vec<i32> = Vec::new();
    let mut idxs: Ghost<Seq<int>> = Ghost(Seq::empty());
    let mut i: usize = 0;
    while i < arr.len()
        invariant 0 <= i as int <= arr@.len()
        invariant res@.len() == idxs@.len()
        invariant forall|j: int| 0 <= j < idxs@.len() ==> #[trigger] res@[j] == #[trigger] arr@[idxs@[j]]
        invariant forall|j: int| 0 <= j < idxs@.len() ==> arr@[idxs@[j]] % 2 == 0
        invariant forall|j: int| 0 <= j < idxs@.len() ==> 0 <= idxs@[j]
        invariant forall|j: int| 0 <= j < idxs@.len() ==> idxs@[j] < i as int
        invariant forall|j: int, k: int| 0 <= j < k < idxs@.len() ==> idxs@[j] < idxs@[k]
        invariant forall|j: int| 0 <= j < i as int && arr@[j] % 2 == 0 ==> exists|t: int| 0 <= t < idxs@.len() && idxs@[t] == j
    {
        let v = arr[i];
        if v % 2 == 0 {
            res.push(v);
            idxs = Ghost(idxs@.push(i as int));
        }
        i += 1;
    }
    proof {
        assert(forall|k: int| 0 <= k < res@.len() ==> res@[k] % 2 == 0) by {
            assert forall|k: int| 0 <= k < res@.len() ==> res@[k] % 2 == 0 by {
                if 0 <= k && k < res@.len() {
                    assert(res@[k] == arr@[idxs@[k]]);
                    assert(arr@[idxs@[k]] % 2 == 0);
                }
            }
        }

        assert(forall|x: i32| #[trigger] res@.contains(x) ==> arr@.contains(x)) by {
            assert forall|x: i32| #[trigger] res@.contains(x) ==> arr@.contains(x) by {
                if res@.contains(x) {
                    let j = choose|j: int| 0 <= j < res@.len() && #[trigger] res@[j] == x;
                    let n = idxs@[j];
                    assert(0 <= n);
                    assert(n < arr@.len()) by {
                        assert(n < i as int);
                        assert(i as int <= arr@.len());
                    }
                    assert(arr@[n] == x);
                    assert(arr@.contains(x)) by {
                        assert(exists|k: int| 0 <= k < arr@.len() && #[trigger] arr@[k] == x);
                    }
                }
            }
        }
        assert(forall|x: i32| !arr@.contains(x) ==> !res@.contains(x)) by {
            assert forall|x: i32| !arr@.contains(x) ==> !res@.contains(x) by {
                if !arr@.contains(x) {
                    assert(!res@.contains(x)) by {
                        if res@.contains(x) {
                            assert(arr@.contains(x));
                        }
                    }
                }
            }
        }

        assert(forall|x: i32| arr@.contains(x) && x % 2 == 0 ==> res@.contains(x)) by {
            assert forall|x: i32| arr@.contains(x) && x % 2 == 0 ==> res@.contains(x) by {
                if arr@.contains(x) && x % 2 == 0 {
                    let j = choose|j: int| 0 <= j < arr@.len() && #[trigger] arr@[j] == x;
                    assert(0 <= j && j < arr@.len());
                    assert(res@.contains(x)) by {
                        let t = choose|t: int| 0 <= t < idxs@.len() && idxs@[t] == j;
                        assert(0 <= t && t < idxs@.len()) by {
                            assert(j < i as int);
                            assert(exists|t2: int| 0 <= t2 < idxs@.len() && idxs@[t2] == j);
                        }
                        assert(res@[t] == arr@[idxs@[t]]);
                        assert(arr@[idxs@[t]] == arr@[j]);
                        assert(res@[t] == x);
                        assert(res@.contains(x)) by {
                            assert(exists|k: int| 0 <= k < res@.len() && #[trigger] res@[k] == x);
                        }
                    }
                }
            }
        }

        assert(forall|k: int, l: int|
            0 <= k < l < res@.len() ==>
            exists|n: int, m: int|
                0 <= n < m < arr@.len() &&
                #[trigger] res@[k] == #[trigger] arr@[n] &&
                #[trigger] res@[l] == #[trigger] arr@[m]
        ) by {
            assert forall|k: int, l: int|
                0 <= k < l < res@.len() ==>
                exists|n: int, m: int|
                    0 <= n < m < arr@.len() &&
                    #[trigger] res@[k] == #[trigger] arr@[n] &&
                    #[trigger] res@[l] == #[trigger] arr@[m]
            by {
                if 0 <= k && k < l && l < res@.len() {
                    let n0 = idxs@[k];
                    let m0 = idxs@[l];
                    assert(0 <= n0);
                    assert(0 <= m0);
                    assert(n0 < m0) by {
                        assert(idxs@[k] < idxs@[l]);
                    }
                    assert(n0 < arr@.len()) by {
                        assert(n0 < i as int);
                        assert(i as int <= arr@.len());
                    }
                    assert(m0 < arr@.len()) by {
                        assert(m0 < i as int);
                        assert(i as int <= arr@.len());
                    }
                    assert(res@[k] == arr@[n0]);
                    assert(res@[l] == arr@[m0]);
                    assert(exists|n: int, m: int|
                        0 <= n < m < arr@.len() &&
                        #[trigger] res@[k] == #[trigger] arr@[n] &&
                        #[trigger] res@[l] == #[trigger] arr@[m]
                    ) by {
                        let n = n0;
                        let m = m0;
                        assert(0 <= n && n < m && m < arr@.len());
                        assert(res@[k] == arr@[n]);
                        assert(res@[l] == arr@[m]);
                    }
                }
            }
        }
    }
    return res;
}
// </vc-code>

fn main() {
}

}