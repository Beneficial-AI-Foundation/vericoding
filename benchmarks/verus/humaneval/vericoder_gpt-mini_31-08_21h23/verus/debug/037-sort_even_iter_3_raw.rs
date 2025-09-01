```vc-helpers
spec fn seq_even(s: Seq<i32>) -> Seq<i32> {
    if s.len() == 0 {
        Seq::empty()
    } else if s.len() == 1 {
        Seq::unit(s[0])
    } else {
        Seq::cons(s[0], seq_even(s.skip(2)))
    }
}

spec fn count_even_prefix(s: Seq<i32>, i: int, x: i32) -> int {
    if i == 0 {
        0
    } else {
        let prev = count_even_prefix(s, i - 1, x);
        prev + if (i - 1) % 2 == 0 && s[i - 1] == x { 1 } else { 0 }
    }
}

// Lemma: swapping two indices in a sequence preserves counts (for i32)
proof fn lemma_swap_counts_i32(s: Seq<i32>, i: int, j: int)
    requires 0 <= i < s.len()
    requires 0 <= j < s.len()
    ensures forall|x: i32| count(s.update(i, s[j]).update(j, s[i]), x) == count(s, x)
{
    if i == j {
        forall|x: i32| {
            assert(s.update(i, s[j]).update(j, s[i]) == s);
            assert(count(s.update(i, s[j]).update(j, s[i]), x) == count(s, x));
        }
    } else {
        let a = s[i];
        let b = s[j];
        forall|x: i32| {
            let s1 = s.update(i, b);
            let s2 = s1.update(j, a);
            // apply lemma for single updates via inner_expr_lemma_update_effect_on_count
            assert(inner_expr_lemma_update_effect_on_count(s, i, b, x));
            assert(inner_expr_lemma_update_effect_on_count(s1, j, a, x));
            if a == b {
                assert(s2 == s);
                assert(count(s2, x) == count(s, x));
            } else {
                if x == a {
                    // a != b, x == a
                    // first update at i: b != x and s[i] == x => count(s1,x) = count(s,x) - 1
                    assert(b != x);
                    assert(a == x);
                    assert(count(s1, x) == count(s, x) - 1);
                    // second update at j: a == x and s1[j] == b != x => count(s2,x) = count(s1,x) + 1
                    assert(s1[j] == b);
                    assert(count(s2, x) == count(s1, x) + 1);
                    assert(count(s2, x) == count(s, x));
                } else if x == b {
                    // a != b, x == b
                    // first update at i: b == x and s[i] != x => count(s1,x) = count(s,x) + 1
                    assert(b == x);
                    assert(a != x);
                    assert(count(s1, x) == count(s, x) + 1);
                    // second update at j: a != x and s1[j] == b == x => count(s2,x) = count(s1,x) - 1
                    assert(s1[j] == b);
                    assert(count(s2, x) == count(s1, x) - 1);
                    assert(count(s2, x) == count(s, x));
                } else {
                    // x != a && x != b: neither update affects count
                    // first update: v != x and s[i] != x (or v != x and s[i] != x) etc. but from lemma we can conclude no change
                    // instantiate both lemmas to get no change
                    // For first update:
                    if b == x {
                        // handled above
                        assume(false);
                    } else {
                        if a == x {
                            // handled above
                            assume(false);
                        } else {
                            // both different
                            assert(count(s1, x) == count(s, x));
                            assert(count(s2, x) == count(s1, x));
                            assert(count(s2, x) == count(s, x));
                        }
                    }
                }
            }
        }
    }
}
```

```vc-code
{
    let mut res = l.clone();
    let n = res.len();
    let mut i: int = 0;
    // Outer loop: iterate over even indices 0,2,4,...
    while i < n
        invariant 0 <= i <= n
        invariant i % 2 == 0
        invariant res.len() == l.len()
        invariant permutes(res@, l@)
        invariant forall|k: int| 0 <= k < n && k % 2 == 1 ==> res[k] == l[k]
        // all even indices < i are <= any even index >= i
        invariant forall|a: int, b: int|
            0 <= a < i && a % 2 == 0 && i <= b < n && b % 2 == 0 ==> res[a] <= res[b]
    {
        if i + 1 >= n {
            // Either i is last index or beyond last; in both cases nothing to do
            i += 2;
            continue;
        }
        // find minimal element among even indices in [i, n)
        let mut m: int = i;
        let mut j: int = i + 2;
        while j < n
            invariant i + 2 <= j <= n
            invariant 0 <= m < n
            invariant i % 2 == 0
            invariant m % 2 == 0
            // m is index of minimal element among even indices k in [i, j)
            invariant forall|k: int| 0 <= k < n && i <= k < j && k % 2 == 0 ==> res[m] <= res[k]
        {
            if res[j] < res[m] {
                m = j;
            }
            j += 2;
        }
        // Now m is index of minimal even element in [i, n)
        if m != i {
            // perform swap of res[i] and res[m]
            let old_seq = res@;
            res.swap(i as usize, m as usize);
            // show that res@ equals old_seq updated by swapping i and m
            proof {
                // pointwise equality
                forall|k: int| 0 <= k < res.len() ==>
                    if k == i {
                        assert(res@[k] == old_seq[m]);
                    } else if k == m {
                        assert(res@[k] == old_seq[i]);
                    } else {
                        assert(res@[k] == old_seq[k]);
                    };
                // now have pointwise equality; assert sequence equality
                assert(res@ == old_seq.update(i, old_seq[m]).update(m, old_seq[i]));
            }
            // counts preserved by swapping two indices in sequence
            lemma_swap_counts_i32(old_seq, i, m);
            // combine with previous invariant permutes(old_seq, l@) to get permutes(res@, l@)
            proof {
                // from invariant before swap we had permutes(old_seq, l@)
                assert(forall|x: i32| count(old_seq, x) == count(l@, x));
                // from lemma_swap_counts_i32: forall x count(old_seq.update(i, old_seq[m]).update(m, old_seq[i]), x) == count(old_seq, x)
                assert(forall|x: i32| count(res@, x) == count(old_seq, x));
                // combine
                assert(forall|x: i32| count(res@, x) == count(l@, x));
            }
            // odd positions unchanged by swapping two even indices
            proof {
                forall|k: int| 0 <= k < n && k % 2 == 1 ==>
                    assert(res[k] == old_seq[k]);
                // and old_seq[k] == l[k] by invariant
                // combine
                forall|k: int| 0 <= k < n && k % 2 == 1 ==>
                    assert(res[k] == l[k]);
            }
        }
        // Now we placed minimal element at index i; need to show invariant holds for i+2
        // Show that all previous even indices < i+2 are <= any even index >= i+2
        proof {
            // Let i' = i + 2
            let ip = i + 2;
            // We need to prove: forall a < ip with a even, forall b in [ip,n) even, res[a] <= res[b]
            // Consider two cases for a:
            // 1) a < i: by outer invariant before this iteration, res[a] <= any even index >= i; and since ip >= i, it implies res[a] <= res[b]
            // 2) a == i: res[i] is minimal among even indices in [i, n), so res[i] <= res[b]
            forall|a: int, b: int| (0 <= a < ip && a % 2 == 0 && ip <= b && b < n && b % 2 == 0) ==>
            {
                if a < i {
                    // from outer invariant prior to this iteration
                    assert(forall|aa: int, bb: int| 0 <= aa < i && aa % 2 == 0 && i <= bb < n && bb % 2 == 0 ==> res