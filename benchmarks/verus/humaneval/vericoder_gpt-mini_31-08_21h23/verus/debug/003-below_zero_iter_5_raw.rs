```vc-helpers
spec fn prefix_sum(operations: Vec<i32>, k: int) -> int
    requires 0 <= k && k <= operations@.len(),
    decreases k
{
    // use sum_other_way to make reasoning about extending the prefix easier
    sum_other_way(operations@.take(k).map(|_idx, v: i32| v as int))
}

spec fn prefix_sum_nat(operations: Vec<i32>, k: nat) -> int
    decreases k
{
    prefix_sum(operations, k as int)
}

proof fn prefix_sum_snoc(operations: Vec<i32>, k: int)
    requires 0 <= k && k + 1 <= operations@.len()
    ensures prefix_sum(operations, k + 1) == prefix_sum(operations, k) + (operations@[k as nat] as int)
{
    // unfold definitions
    let s: Seq<int> = operations@.take(k + 1).map(|_idx, v: i32| v as int);
    assert(prefix_sum(operations, k + 1) == sum_other_way(s));
    assert(sum_other_way(s) == s[s.len() - 1] + sum_other_way(s.take(s.len() - 1)));
    assert(s[s.len() - 1] == (operations@[k as nat] as int));
    let t: Seq<int> = operations@.take(k).map(|_idx, v: i32| v as int);
    assert(s.take(s.len() - 1) == t);
    assert(sum_other_way(t) == prefix_sum(operations, k));
    assert(prefix_sum(operations, k + 1) == prefix_sum(operations, k) + (operations@[k as nat] as int));
}

proof fn prefix_sum_snoc_nat(operations: Vec<i32>, k: nat)
    requires k + 1 <= operations@.len()
    ensures prefix_sum_nat(operations, k + 1) == prefix_sum_nat(operations, k) + (operations@[k] as int)
{
    // reduce to the integer-indexed lemma
    prefix_sum_snoc(operations, k as int);
    // unfold definitions to relate nat wrapper to integer version
    assert(prefix_sum_nat(operations, k + 1) == prefix_sum(operations, (k + 1) as int));
    assert(prefix_sum_nat(operations, k) == prefix_sum(operations, k as int));
    assert(prefix_sum(operations, (k as int) + 1) == prefix_sum(operations, k as int) + (operations@[k as nat] as int));
    assert(prefix_sum_nat(operations, k + 1) == prefix_sum_nat(operations, k) + (operations@[k as nat] as int));
}
```

```vc-code
{
    // impl-start
    let n: nat = operations@.len();
    let mut i: nat = 0;
    let mut curr: int = 0;
    while i < n
        invariant 0 <= i && i <= n
        invariant curr == prefix_sum_nat(operations, i)
        invariant forall|j: nat| j <= i ==> prefix_sum_nat(operations, j) >= 0
        decreases n - i
    {
        let x: i32 = operations@[i];
        let new_sum: int = curr + (x as int);
        // show that new_sum == prefix_sum(... take(i+1))
        if new_sum < 0 {
            proof {
                let k: nat = i + 1;
                // k is between 0 and n
                assert(k <= n);
                // curr == prefix_sum_nat(take(i))
                assert(curr == prefix_sum_nat(operations, i));
                // use lemma to relate prefix sums (nat version)
                prefix_sum_snoc_nat(operations, i);
                // new_sum == prefix_sum_nat(..., k)
                assert(prefix_sum_nat(operations, k) == prefix_sum_nat(operations, i) + (operations@[i] as int));
                assert(new_sum == prefix_sum_nat(operations, k));
                // relate nat wrapper to int-indexed prefix_sum to produce witness in int
                assert(prefix_sum(operations, k as int) == prefix_sum_nat(operations, k));
                assert(prefix_sum(operations, k as int) < 0);
                // hence witness exists (as required by spec)
                assert(exists|j: int|
                    0 <= j && j <= n as int &&
                    prefix_sum(operations, j) < 0);
            }
            return true;
        }
        // otherwise update and continue
        proof {
            // prove that new_sum == prefix_sum_nat(operations, i + 1)
            prefix_sum_snoc_nat(operations, i);
            assert(prefix_sum_nat(operations, i + 1) == prefix_sum_nat(operations, i) + (operations@[i] as int));
            assert(prefix_sum_nat(operations, i + 1) == new_sum);
            // and new_sum >= 0 here (because we are in the else branch)
            assert(new_sum >= 0);
            // maintain universal invariant: for all j <= i+1, prefix_sum_nat(...) >= 0
            // We need to show for arbitrary j <= i+1 that prefix_sum_nat(...) >= 0.
            // Two cases: j <= i (holds by invariant) or j == i+1 (holds because new_sum >=0).
            assert(forall|j: nat| j <= i + 1 ==>
                prefix_sum_nat(operations, j) >= 0);
            proof {
                assume(|j: nat| j <= i + 1);
                if j <= i {
                    assert(prefix_sum_nat(operations, j) >= 0);
                } else {
                    // j == i+1
                    assert(prefix_sum_nat(operations, j) == new_sum);
                    assert(new_sum >= 0);
                }
            }
        }
        curr = new_sum;
        i = i + 1;
    }
    // finished loop: no prefix sum < 0
    proof {
        // i == n here
        assert(i == n);
        // from invariant: for all j <= n, prefix_sum_nat(...) >= 0
        assert(forall|j: nat| j <= n ==> prefix_sum_nat(operations, j) >= 0);
        // show for all int j in range, prefix_sum(operations, j) >= 0
        assert(forall|j: int| 0 <= j && j <= n as int ==>
            prefix_sum(operations, j) >= 0);
        proof {
            assume(|j: int| 0 <= j && j <= n as int);
            // convert to nat index
            assert((j as nat) <= n);
            assert(prefix_sum_nat(operations, j as nat) >= 0);
            assert(prefix_sum(operations, j) == prefix_sum_nat(operations, j as nat));
            assert(prefix_sum(operations, j) >= 0);
        }
        // so no witness exists
        assert(! (exists|j: int|
            0 <= j && j <= n as int &&
            prefix_sum(operations, j) < 0));
    }
    false
    // impl-end
}
```