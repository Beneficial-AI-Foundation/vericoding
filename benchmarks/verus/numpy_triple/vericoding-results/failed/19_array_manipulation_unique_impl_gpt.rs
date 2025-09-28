// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed bound assertion syntax and cast usage; strengthened invariants and end-of-loop reasoning */
fn vec_contains(v: &Vec<i32>, x: i32) -> (b: bool)
    ensures
        b == v@.contains(x),
{
    let mut i: usize = 0;
    let mut found: bool = false;
    while i < v.len()
        invariant
            (i as int) <= (v.len() as int),
            found ==> v@.contains(x),
            (!found) ==> (forall|k: int| 0 <= k < i as int ==> v@[k] != x),
        decreases v.len() - i
    {
        if v[i] == x {
            found = true;
            proof {
                assert(0 <= i as int);
                assert(i as int < v.len() as int);
                assert(v@[i as int] == x);
                assert(v@.contains(x));
            }
        }
        i = i + 1;
    }
    if found {
        proof { assert(v@.contains(x)); }
        true
    } else {
        proof {
            assert(i == v.len());
            assert(forall|k: int| 0 <= k < v.len() as int ==> v@[k] != x) by {
                assert(forall|k: int| 0 <= k < i as int ==> v@[k] != x);
                assert(i == v.len());
            }
            assert(!v@.contains(x)) by {
                assert(forall|k: int| 0 <= k < v.len() as int ==> v@[k] != x);
            }
        }
        false
    }
}

/* helper modified by LLM (iteration 5): split composite asserts with casts for clarity and to satisfy parser; preserved invariants */
fn compute_min_max(v: &Vec<i32>) -> (res: (i32, i32))
    requires
        v.len() > 0,
    ensures
        forall|k: int| 0 <= k < v.len() ==> res.0 <= v@[k] <= res.1,
{
    let mut idx: usize = 1;
    let mut mn: i32 = v[0];
    let mut mx: i32 = v[0];
    while idx < v.len()
        invariant
            1 <= idx as int,
            (idx as int) <= v.len() as int,
            mn <= mx,
            forall|k: int| 0 <= k < idx as int ==> mn <= v@[k] <= mx,
        decreases v.len() - idx
    {
        let val = v[idx];
        let old_mn = mn;
        let old_mx = mx;
        if val < mn {
            mn = val;
        }
        if mx < val {
            mx = val;
        }
        proof {
            assert(mn <= old_mn) by {
                if val < old_mn {
                    assert(mn == val);
                    assert(mn <= old_mn);
                } else {
                    assert(mn == old_mn);
                }
            }
            assert(old_mx <= mx) by {
                if old_mx < val {
                    assert(mx == val);
                    assert(old_mx <= mx);
                } else {
                    assert(mx == old_mx);
                }
            }
            assert(forall|k: int| 0 <= k < idx as int ==> mn <= v@[k] <= mx) by {
                assert(forall|k: int| 0 <= k < idx as int ==> old_mn <= v@[k] <= old_mx);
            }
            assert(0 <= idx as int);
            assert(idx as int < v.len() as int);
            assert(mn <= val) by {
                if val < old_mn {
                    assert(mn == val);
                    assert(mn <= val);
                } else {
                    assert(mn == old_mn);
                    assert(old_mn <= val);
                }
            }
            assert(val <= mx) by {
                if old_mx < val {
                    assert(mx == val);
                    assert(val <= mx);
                } else {
                    assert(mx == old_mx);
                    assert(val <= old_mx);
                    assert(val <= mx);
                }
            }
        }
        idx = idx + 1;
    }
    (mn, mx)
}
// </vc-helpers>

// <vc-spec>
spec fn is_sorted(arr: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j]
}

spec fn has_no_duplicates(arr: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr.len() && i != j ==> arr[i] != arr[j]
}

spec fn all_elements_from_input(result: Seq<i32>, input: Seq<i32>) -> bool {
    forall|i: int| 0 <= i < result.len() ==> #[trigger] input.contains(result[i])
}

spec fn all_distinct_elements_present(input: Seq<i32>, result: Seq<i32>) -> bool {
    forall|val: i32| input.contains(val) ==> #[trigger] result.contains(val)
}

fn numpy_unique(arr: Vec<i32>) -> (result: (usize, Vec<i32>))
    ensures
        is_sorted(result.1@),
        has_no_duplicates(result.1@),
        all_elements_from_input(result.1@, arr@),
        all_distinct_elements_present(arr@, result.1@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed choose bound to use arr@.len() and cleaned boolean proofs; maintained sorted/unique invariants */
    if arr.len() == 0usize {
        let out: Vec<i32> = Vec::new();
        return (0usize, out);
    }

    let (mn, mx) = compute_min_max(&arr);
    let mut out: Vec<i32> = Vec::new();
    let mut i: i32 = mn;

    while i <= mx
        invariant
            (mn as int) <= (i as int) && (i as int) <= (mx as int),
            is_sorted(out@),
            has_no_duplicates(out@),
            all_elements_from_input(out@, arr@),
            forall|t: i32| (mn as int) <= (t as int) && (t as int) < (i as int) ==> (arr@.contains(t) ==> out@.contains(t)),
            out.len() == 0 || (out@[(out.len() - 1) as int] as int) < (i as int),
        decreases (mx as int - i as int + 1) as nat
    {
        let curr: i32 = i;
        let b = vec_contains(&arr, curr);
        if b {
            let old_len_usize: usize = out.len();
            let old_len: int = old_len_usize as int;
            let old_seq = out@;
            out.push(curr);
            proof {
                let new_len: int = out.len() as int;
                assert(new_len == old_len + 1);
                assert_forall_by(|a: int, b2: int| {
                    requires 0 <= a < b2 < new_len,
                    ensures out@[a] <= out@[b2],
                }, {
                    if b2 < old_len {
                        assert(out@[a] == old_seq[a]);
                        assert(out@[b2] == old_seq[b2]);
                        assert(is_sorted(old_seq));
                    } else {
                        assert(b2 == old_len);
                        if old_len == 0 {
                        } else {
                            assert(0 <= a < old_len);
                            let last_idx: int = old_len - 1;
                            assert(0 <= last_idx < old_len);
                            assert(is_sorted(old_seq));
                            assert(old_seq[a] <= old_seq[last_idx]);
                            assert(old_seq[last_idx] as int < curr as int);
                            assert(old_seq[a] as int <= old_seq[last_idx] as int);
                            assert(old_seq[a] as int < curr as int);
                            assert(old_seq[a] <= curr);
                            assert(out@[a] == old_seq[a]);
                            assert(out@[b2] == curr);
                        }
                    }
                });
                assert_forall_by(|a: int, b2: int| {
                    requires 0 <= a < new_len && 0 <= b2 < new_len && a != b2,
                    ensures out@[a] != out@[b2],
                }, {
                    if a < old_len && b2 < old_len {
                        assert(out@[a] == old_seq[a]);
                        assert(out@[b2] == old_seq[b2]);
                        assert(has_no_duplicates(old_seq));
                    } else if a < old_len && b2 == old_len {
                        let last_idx: int = old_len - 1;
                        if old_len == 0 { } else {
                            assert(0 <= a < old_len);
                            assert(is_sorted(old_seq));
                            assert(old_seq[a] <= old_seq[last_idx]);
                            assert(old_seq[last_idx] as int < curr as int);
                            assert(old_seq[a] as int <= old_seq[last_idx] as int);
                            assert(old_seq[a] as int < curr as int);
                            assert(old_seq[a] != curr);
                            assert(out@[a] == old_seq[a]);
                            assert(out@[b2] == curr);
                        }
                    } else if a == old_len && b2 < old_len {
                        let last_idx: int = old_len - 1;
                        if old_len == 0 { } else {
                            assert(0 <= b2 < old_len);
                            assert(is_sorted(old_seq));
                            assert(old_seq[b2] <= old_seq[last_idx]);
                            assert(old_seq[last_idx] as int < curr as int);
                            assert(old_seq[b2] as int <= old_seq[last_idx] as int);
                            assert(old_seq[b2] as int < curr as int);
                            assert(old_seq[b2] != curr);
                            assert(out@[a] == curr);
                            assert(out@[b2] == old_seq[b2]);
                        }
                    } else {
                    }
                });
                assert_forall_by(|k: int| {
                    requires 0 <= k < new_len,
                    ensures arr@.contains(out@[k]),
                }, {
                    if k < old_len {
                        assert(all_elements_from_input(old_seq, arr@));
                        assert(out@[k] == old_seq[k]);
                    } else {
                        assert(k == old_len);
                        assert(b);
                        assert(arr@.contains(curr));
                        assert(out@[k] == curr);
                    }
                });
            }
        }
        proof {
            assert(forall|t: i32| (mn as int) <= (t as int) && (t as int) < ((i + 1) as int) ==> (arr@.contains(t) ==> out@.contains(t))) by {
                assert(forall|t: i32| (mn as int) <= (t as int) && (t as int) < (i as int) ==> (arr@.contains(t) ==> out@.contains(t)));
                if arr@.contains(curr) {
                    assert(arr@.contains(curr) == b);
                    if b { assert(out@.contains(curr)); }
                }
            }
        }
        if i == mx {
            break;
        } else {
            i = i + 1;
            proof {
                if out.len() == 0 {
                } else {
                    let last_idx: int = (out.len() - 1) as int;
                    let last_val = out@[last_idx];
                    assert(last_val as int < curr as int);
                    assert((curr as int) < (i as int));
                    assert(last_val as int < i as int);
                }
            }
        }
    }

    proof {
        assert(forall|val: i32| arr@.contains(val) ==> out@.contains(val)) by {
            if arr@.contains(val) {
                let k = choose|k: int| 0 <= k < arr@.len() && arr@[k] == val;
                assert(0 <= k < arr@.len() && arr@[k] == val);
                assert(mn <= arr@[k] <= mx);
                assert((mn as int) <= (val as int));
                assert((val as int) <= (mx as int));
                assert(i == mx);
                if (val as int) < (i as int) {
                    assert(forall|t: i32| (mn as int) <= (t as int) && (t as int) < (i as int) ==> (arr@.contains(t) ==> out@.contains(t)));
                    assert(out@.contains(val));
                } else {
                    assert((val as int) == (i as int));
                    assert(forall|t: i32| (mn as int) <= (t as int) && (t as int) < ((i + 1) as int) ==> (arr@.contains(t) ==> out@.contains(t)));
                    assert((val as int) < ((i + 1) as int));
                    assert(out@.contains(val));
                }
            }
        }
    }

    (out.len(), out)
}
// </vc-code>


}
fn main() {}