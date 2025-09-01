```vc-helpers
proof fn sum_take_map_succ(s: Seq<i32>, k: int)
    requires
        0 <= k && k + 1 <= s.len(),
    ensures
        sum(s.take(k + 1).map(|_idx, v: i32| v as int))
            == sum(s.take(k).map(|_idx, v: i32| v as int)) + (s@[k] as int),
    decreases
        k,
{
    if k == 0 {
        assert(s.take(0).map(|_i, v: i32| v as int).len() == 0);
        assert(sum(s.take(0).map(|_i, v: i32| v as int)) == 0);

        assert(s.take(1).map(|_i, v: i32| v as int).len() == 1);
        assert(s.take(1).map(|_i, v: i32| v as int)@[0] == s@[0] as int);
        assert(sum(s.take(1).map(|_i, v: i32| v as int)) == s@[0] as int);
    } else {
        sum_take_map_succ(s, k - 1);

        let left = s.take(k + 1).map(|_i, v: i32| v as int);
        let right = s.take(k).map(|_i, v: i32| v as int) + seq![s@[k] as int];

        // lengths equal
        assert(left.len() == right.len());

        // element-wise equality
        assert(forall|j: int|
            0 <= j && j < left.len() ==>
                left@[j] == right@[j]
        );

        assert(left == right);

        // sum of seq![x] is x
        assert(sum(seq![s@[k] as int]) == s@[k] as int);

        // sum of concatenation equals sum of parts
        assert(sum(right) == sum(s.take(k).map(|_i, v: i32| v as int)) + sum(seq![s@[k] as int]));
        assert(sum(right) == sum(s.take(k).map(|_i, v: i32| v as int)) + (s@[k] as int));
        assert(sum(left) == sum(right));
    }
}
```

```vc-code
{
    let n = operations@.len();
    let mut i: int = 0;
    let mut acc: int = 0;
    while i < n
        invariant 0 <= i && i <= n;
        invariant acc == sum(operations@.take(i).map(|_idx, j: i32| j as int));
        invariant forall|j: int| 0 <= j && j <= i ==> sum(operations@.take(j).map(|_idx, j: i32| j as int)) >= 0;
        decreases n - i;
    {
        let next = acc + (operations@[i] as int);
        if next < 0 {
            proof {
                // sum(take(i+1)) == acc + operations@[i]
                sum_take_map_succ(operations@, i);
                assert(acc == sum(operations@.take(i).map(|_idx, j: i32| j as int)));
                assert(sum(operations@.take(i + 1).map(|_idx, j: i32| j as int)) == acc + (operations@[i] as int));
                assert(sum(operations@.take(i + 1).map(|_idx, j: i32| j as int)) == next);

                // witness i+1 satisfies the postcondition existence
                assert(0 <= i + 1 && i + 1 <= n);
                assert(next < 0);
                assert(0 <= i + 1 && i + 1 <= n && sum(operations@.take(i + 1).map(|_idx, j: i32| j as int)) < 0);
                assert(exists|j: int| 0 <= j && j <= n && sum(operations@.take(j).map(|_idx, j: i32| j as int)) < 0);
            }
            return true;
        }
        proof {
            // show sum(take(i+1)) == next and establish non-negativity up to i+1
            sum_take_map_succ(operations@, i);
            assert(acc == sum(operations@.take(i).map(|_idx, j: i32| j as int)));
            assert(sum(operations@.take(i + 1).map(|_idx, j: i32| j as int)) == acc + (operations@[i] as int));
            assert(sum(operations@.take(i + 1).map(|_idx, j: i32| j as int)) == next);

            // next >= 0 because we are in the else branch (not next < 0)
            assert(next >= 0);

            // prove forall j <= i+1 sum(...) >= 0
            assert(forall|j: int| 0 <= j && j <= i + 1 ==>
                sum(operations@.take(j).map(|_idx, j: i32| j as int)) >= 0);
            proof {
                fix j;
                assume Hj: 0 <= j && j <= i + 1;
                if j <= i {
                    // use the previous invariant for j <= i
                    assert(sum(operations@.take(j).map(|_idx, j: i32| j as int)) >= 0);
                } else {
                    // j == i+1
                    assert(j == i + 1);
                    assert(sum(operations@.take(j).map(|_idx, j: i32| j as int)) == next);
                    assert(next >= 0);
                }
            }
        }
        acc = next;
        i = i + 1;
    }
    proof {
        // at loop end, i == n, and all prefix sums are >= 0
        assert(forall|j: int| 0 <= j && j <= n ==>
            sum(operations@.take(j).map(|_idx, j: i32| j as int)) >= 0);
        proof {
            fix j;
            assume Hj: 0 <= j && j <= n;
            // instantiate with i = n
            // from loop invariant we have the forall up to n
            assert(sum(operations@.take(j).map(|_idx, j: i32| j as int)) >= 0);
        }
        // therefore no prefix sum is < 0
        assert(!exists|j: int| 0 <= j && j <= n &&
            sum(operations@.take(j).map(|_idx, j: i32| j as int)) < 0);
    }
    false
}
```