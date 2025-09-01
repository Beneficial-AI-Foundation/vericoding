```vc-helpers
/* No helpers needed for this proof. */
```

```vc-code
{
    // impl-start
    let n: usize = lists.len();
    let mut min_idx: usize = 0;
    let mut min_len: usize = lists[0].len();
    let mut i: usize = 1;
    while i < n
        invariant i <= n;
        invariant min_idx < n;
        invariant min_len == lists[min_idx].len();
        invariant forall|j: usize| j < i ==> min_len <= lists[j].len();
        decreases n - i;
    {
        let cur_len: usize = lists[i].len();
        if cur_len < min_len {
            min_len = cur_len;
            min_idx = i;
        }
        i += 1;
    }

    proof {
        // At loop exit, i == n
        assert(i == n);

        // witness for existence: min_idx as int
        assert(min_idx < n);
        assert(min_len == lists[min_idx].len());
        {
            let k0: int = min_idx as int;
            assert(0 <= k0);
            assert(k0 < (n as int));
            assert(min_len == lists[k0 as usize].len());
            assert(exists|k: int| 0 <= k && k < (n as int) && min_len == lists[k as usize].len());
        }

        // and minimality (forall) follows from the loop invariant with i == n
        assert(forall|jj: usize| jj < n ==> min_len <= lists[jj].len());

        // convert the forall over usize to forall over int
        assert(forall|j: int| 0 <= j && j < (n as int) ==> min_len <= lists[j as usize].len());
        {
            fix |j: int|;
            assume(0 <= j && j < (n as int));
            let ju: usize = j as usize;
            // from 0 <= j < n we get ju < n
            assert(ju < n);
            // use the forall over usize proven above
            assert(min_len <= lists[ju].len());
        }
    }

    min_len
    // impl-end
}
```