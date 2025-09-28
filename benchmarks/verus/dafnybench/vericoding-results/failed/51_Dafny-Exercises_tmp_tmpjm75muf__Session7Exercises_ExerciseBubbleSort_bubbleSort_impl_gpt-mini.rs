use vstd::prelude::*;

verus! {

spec fn sorted_seg(a: Seq<int>, i: int, j: int) -> bool
    recommends 0 <= i <= j <= a.len()
{
    forall|l: int, k: int| i <= l <= k < j ==> a[l] <= a[k]
}

// <vc-helpers>
spec fn seq_swap(s: Seq<int>, i: int, j: int) -> Seq<int>
    requires 0 <= i < s.len() && 0 <= j < s.len()
{
    s.update(i, s@[j]).update(j, s@[i])
}

proof fn seq_swap_preserves_multiset(s: Seq<int>, i: int, j: int)
    requires 0 <= i < s.len() && 0 <= j < s.len()
    ensures s.to_multiset() == seq_swap(s, i, j).to_multiset()
{
    proof {
        forall|v: int| {
            // counts are preserved because only positions i and j are swapped
            if i == j {
                assert(s.to_multiset().count(v) == seq_swap(s, i, j).to_multiset().count(v));
            } else {
                // compute counts by cases on values at i and j
                let vi = s@[i];
                let vj = s@[j];
                if vi == vj {
                    assert(s.to_multiset().count(v) == seq_swap(s, i, j).to_multiset().count(v));
                } else {
                    // when vi != vj, counts for vi and vj are exchanged, others unchanged
                    assert(s.to_multiset().count(v) == seq_swap(s, i, j).to_multiset().count(v));
                }
            }
        }
    }
}

proof fn swap_preserves_subrange_multiset(s: Seq<int>, c: int, f: int, i: int, j: int)
    requires 0 <= c <= i < f && 0 <= c <= j < f && f <= s.len()
    ensures s.subrange(c, f).to_multiset() == seq_swap(s, i, j).subrange(c, f).to_multiset()
{
    proof {
        seq_swap_preserves_multiset(s, i, j);
        assert(s.to_multiset() == seq_swap(s, i, j).to_multiset());
        forall|v: int| {
            assert(s.subrange(c, f).to_multiset().count(v) == seq_swap(s, i, j).subrange(c, f).to_multiset().count(v));
        }
    }
}

proof fn extend_sorted_with_geq(a: Seq<int>, c: int, k: int, x: int)
    requires 0 <= c <= k && k < a.len()
    requires sorted_seg(a, c, k)
    requires forall|t: int| c <= t < k ==> a@[t] <= x
    ensures sorted_seg(a.update(k, x), c, k+1)
{
    proof {
        forall|l: int, r: int| c <= l <= r < k+1 ==>
        {
            if r < k {
                // both indices in original sorted segment
                assert(a.update(k, x)@[l] <= a.update(k, x)@[r]);
                assert(a@[l] <= a@[r]);
            } else {
                if l < k {
                    // l in original, r == k
                    assert(a.update(k, x)@[l] <= a.update(k, x)@[r]);
                    assert(a@[l] <= x);
                } else {
                    // l == k == r
                    assert(a.update(k, x)@[l] <= a.update(k, x)@[r]);
                }
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn bubble_sort(a: &mut Vec<int>, c: usize, f: usize)
    requires 
        0 <= c <= f <= old(a).len(),
    ensures 
        sorted_seg(a@, c as int, f as int),
        a@.subrange(c as int, f as int).to_multiset() == old(a)@.subrange(c as int, f as int).to_multiset(),
        a@.subrange(0, c as int) == old(a)@.subrange(0, c as int),
        a@.subrange(f as int, a@.len() as int) == old(a)@.subrange(f as int, old(a)@.len() as int),
// </vc-spec>
// <vc-code>
{
    let old_seq: Seq<int> = a@;

    if f <= c + 1 {
        proof {
            assert(a@.subrange(c as int, f as int).to_multiset() == old_seq.subrange(c as int, f as int).to_multiset());
            assert(a@.subrange(0, c as int) == old_seq.subrange(0, c as int));
            assert(a@.subrange(f as int, a@.len() as int) == old_seq.subrange(f as int, old_seq.len()));
            assert(sorted_seg(a@, c as int, f as int));
        }
        return;
    }

    let mut k: usize = c;
    while k < f
        invariant c <= k && k <= f,
        invariant a@.len() == old_seq.len(),
        invariant a@.subrange(0, c as int) == old_seq.subrange(0, c as int),
        invariant a@.subrange(f as int, a@.len() as int) == old_seq.subrange(f as int, old_seq.len()),
        invariant a@.subrange(c as int, f as int).to_multiset() == old_seq.subrange(c as int, f as int).to_multiset(),
        invariant sorted_seg(a@, c as int, k as int),
        invariant forall|t: int, s: int| c as int <= t < k as int && k as int <= s < f as int ==> a@[t as int] <= a@[s as int]
    {
        let mut m: usize = k;
        let mut i: usize = k + 1;
        while i < f
            invariant k <= m && m < f,
            invariant k + 1 <= i && i <= f,
            invariant forall|t: int| (k as int) <= t < (i as int) ==> a@[m as int] <= a@[t as int]
        {
            if a.get(i) < a.get(m) {
                m = i;
            }
            i = i + 1;
        }

        if m != k {
            let cur: Seq<int> = a@;
            proof {
                // from inner loop exit: forall s in [k,f) cur[m] <= cur[s]
                assert(forall|s: int| k as int <= s < f as int ==> cur@[m as int] <= cur@[s as int]);

                // from outer invariants: sorted_seg(cur, c, k)
                assert(sorted_seg(cur, c as int, k as int));

                // show forall t in [c,k) cur[t] <= cur[m] using outer invariant forall t<k, k<=s<f ==> a[t]<=a[s], pick s=m
                assert(forall|t: int| c as int <= t < k as int ==> cur@[t as int] <= cur@[m as int]) by {
                    forall|t: int| c as int <= t < k as int ==>
                    {
                        assert(c as int <= t && t < k as int);
                        assert(k as int <= m as int && m as int < f as int);
                        assert(cur@[t as int] <= cur@[m as int]);
                    }
                };
            }

            // perform swap
            a.swap(m, k);

            proof {
                // multiset for subrange preserved by swap
                swap_preserves_subrange_multiset(cur, c as int, f as int, k as int, m as int);
                // combine with previous invariant that cur.subrange(c,f) equals old_seq.subrange(c,f)
                assert(cur.subrange(c as int, f as int).to_multiset() == old_seq.subrange(c as int, f as int).to_multiset());
                assert(a@.subrange(c as int, f as int).to_multiset() == old_seq.subrange(c as int, f as int).to_multiset());

                // show sorted_seg for extended prefix c..k+1
                // use extend_sorted_with_geq on cur with x = cur[m]
                extend_sorted_with_geq(cur, c as int, k as int, cur@[m as int]);
                // a@ equals seq_swap(cur, k, m)
                assert(a@ == seq_swap(cur, k as int, m as int));
                // since m >= k+1, the subrange c..k+1 of a@ equals that of cur.update(k, cur[m])
                assert(a@.subrange(c as int, (k as int) + 1) == cur.update(k as int, cur@[m as int]).subrange(c as int, (k as int) + 1));
                // from extend_sorted_with_geq, cur.update(k,cur[m]) is sorted on c..k+1
                assert(sorted_seg(cur.update(k as int, cur@[m as int]), c as int, (k as int) + 1));
                // hence a@ is sorted on c..k+1
                assert(sorted_seg(a@, c as int, (k as int) + 1));

                // preserve the relation between prefix and suffix: forall t in [c,k+1) and s in [k+1,f) a[t] <= a[s]
                assert(forall|t: int, s: int| c as int <= t < (k as int + 1) && (k as int + 1) <= s < f as int ==> a@[t as int] <= a@[s as int]) by {
                    forall|t: int, s: int| c as int <= t < (k as int + 1) && (k as int + 1) <= s < f as int ==>
                    {
                        if t < k as int {
                            // t < k: use old invariant (for t < k and k <= s < f cur[t] <= cur[s])
                            assert(cur@[t as int] <= cur@[s as int] || cur@[t as int] <= cur@[k as int]);
                            assert(a@[t as int] <= a@[s as int]);
                        } else {
                            // t == k: a@[k] == cur@[m]; need cur[m] <= a@[s]
                            assert(cur@[m as int] <= cur@[s as int]);
                            assert(a@[t as int] <= a@[s as int]);
                        }
                    }
                };
            }
        }

        k = k + 1;
    }

    proof {
        // at loop exit k == f
        assert(k == f);
        assert(sorted_seg(a@, c as int, f as int));
        assert(a@.subrange(c as int, f as int).to_multiset() == old_seq.subrange(c as int, f as int).to_multiset());
        assert(a@.subrange(0, c as int) == old_seq.subrange(0, c as int));
        assert(a@.subrange(f as int, a@.len() as int) == old_seq.subrange(f as int, old_seq.len()));
    }
}
// </vc-code>

fn main() {
}

}