```vc-helpers
// No helper functions needed for this implementation.
```

```vc-code
{
    // impl-start
    let n: int = s.len() as int;

    let mut j: int = 0;
    let mut k: int = 0;
    while k <= n
        invariant 0 <= j && j <= n
        invariant 0 <= k && k <= n
        invariant forall|t: int| 0 <= t < k ==> exists|idx: int| 0 <= idx < j && s[idx] == t as i32
        invariant forall|idx: int| 0 <= idx < j ==> (s[idx] as int) < k
    {
        // advance j to the first index with s[j] >= k
        while j < n && (s[j] as int) < k
            invariant 0 <= j && j <= n
            invariant 0 <= k && k <= n
            invariant forall|t: int| 0 <= t < k ==> exists|idx: int| 0 <= idx < j && s[idx] == t as i32
            invariant forall|idx: int| 0 <= idx < j ==> (s[idx] as int) < k
        {
            j += 1;
        }

        if j < n && (s[j] as int) == k {
            // include this occurrence and move to next candidate
            j += 1;
            k += 1;
        } else {
            // no occurrence of k in s
            break;
        }
    }

    let v: i32 = k as i32;

    proof {
        // 0 <= v
        assert(0 <= k);
        assert(0 <= v);

        // From the loop invariants at exit:
        // 1) forall t < k . exists idx < j . s[idx] == t
        assert(
            forall|t: int|
                0 <= t < k ==>
                    exists|idx: int| 0 <= idx < j && s[idx] == t as i32
        );

        // 2) forall idx < j . s[idx] < k
        assert(
            forall|idx: int|
                0 <= idx < j ==>
                    (s[idx] as int) < k
        );

        // Also, after the inner while we have either j == n or s[j] >= k.
        // And the outer loop broke only when !(j < n && s[j] == k), so either j == n or s[j] > k.
        assert(j == n || (j < n && (s[j] as int) >= k));
        assert(!(j < n && (s[j] as int) == k));

        // Show there is no index in 0..n-1 with s[idx] == k.
        // If idx < j then s[idx] < k (by invariant). If idx >= j then:
        //   - if j == n then no such idx.
        //   - if j < n then s[idx] >= s[j] > k, so cannot be equal to k.
        assert(!(exists|idx: int| 0 <= idx && idx < n && s[idx] as int == k));
        {
            // proof of the above assertion
            proof {
                by_contradiction {
                    assume H: exists|idx: int| 0 <= idx && idx < n && s[idx] as int == k;
                    reveal_exists!((|idx: int| 0 <= idx && idx < n && s[idx] as int == k), H);
                    let idx0 = H.witness;
                    assert(0 <= idx0 && idx0 < n);
                    // case idx0 < j
                    if idx0 < j {
                        assert((s[idx0] as int) < k); // from invariant
                        assert((s[idx0] as int) == k); // from H
                        assert(false);
                    } else {
                        // idx0 >= j
                        if j == n {
                            // impossible since idx0 < n
                            assert(false);
                        } else {
                            // j < n and s[j] >= k, and not equal (because loop broke),
                            // hence s[j] > k, and since array sorted, s[idx0] >= s[j] > k,
                            // contradicts s[idx0] == k.
                            assert((s[j] as int) > k);
                            assert((s[idx0] as int) >= (s[j] as int));
                            assert((s[idx0] as int) > k);
                            assert(false);
                        }
                    }
                }
            }
        }

        // Therefore forall i < n . s[i] != v
        assert(forall|idx: int| 0 <= idx && idx < n ==> s[idx] != v);

        // For all m < v, we have existence from invariant 1.
        assert(forall|m: int|
            0 <= m && m < k ==>
                exists|idx: int| 0 <= idx && idx < j && s[idx] == m as i32
        );

        // Strengthen to the required postcondition:
        // forall m: 0 <= m < v && s[m] != v ==> exists j . s[j] == m
        // Since for all m < v we already have an index with s[...] == m, the implication holds.
        assert(forall|m: int|
            0 <= m && m < v && s[m] != v ==>
                exists|idx: int| 0 <= idx && idx < n && s[idx] == m as i32
        );
    }

    v
    // impl-end
}
```