```vc-helpers
// <vc-helpers>
proof fn adj_le_rec(s: Seq<i32>, n: nat, i: int, j: int)
    requires n == s.len()
    requires 0 <= i && i < j && j < (n as int)
    requires forall|k: int| 0 <= k < ((n as int) - 1) ==> s@.index(k) <= s@.index(k+1)
    decreases ((j - i) as nat)
{
    if (j - i) == 1 {
        // base case: adjacent
        assert(s@.index(i) <= s@.index(j));
        return;
    } else {
        // prove s[i] <= s[j] by transitivity via i+1
        // i < j and j < n => i < n-1, so adjacency at i holds
        assert(0 <= i && i < (n as int) - 1);
        assert(s@.index(i) <= s@.index(i + 1));
        adj_le_rec(s, n, i + 1, j);
        assert(s@.index(i + 1) <= s@.index(j));
        assert(s@.index(i) <= s@.index(j));
        return;
    }
}

proof fn adjacent_le_implies_global(s: Seq<i32>, n: nat)
    requires n == s.len()
    requires forall|k: int| 0 <= k < ((n as int) - 1) ==> s@.index(k) <= s@.index(k+1)
    ensures forall|i: int, j: int| 0 <= i < j < (n as int) ==> s@.index(i) <= s@.index(j)
{
    if n <= 1 {
        return;
    }
    assert(forall|a: int, b: int| 0 <= a < b < (n as int) ==> s@.index(a) <= s@.index(b)) by {
        fix a, b;
        assume(0 <= a && a < b && b < (n as int));
        adj_le_rec(s, n, a, b);
    };
    return;
}

proof fn adj_ge_rec(s: Seq<i32>, n: nat, i: int, j: int)
    requires n == s.len()
    requires 0 <= i && i < j && j < (n as int)
    requires forall|k: int| 0 <= k < ((n as int) - 1) ==> s@.index(k) >= s@.index(k+1)
    decreases ((j - i) as nat)
{
    if (j - i) == 1 {
        assert(s@.index(i) >= s@.index(j));
        return;
    } else {
        assert(0 <= i && i < (n as int) - 1);
        assert(s@.index(i) >= s@.index(i + 1));
        adj_ge_rec(s, n, i + 1, j);
        assert(s@.index(i + 1) >= s@.index(j));
        assert(s@.index(i) >= s@.index(j));
        return;
    }
}

proof fn adjacent_ge_implies_global(s: Seq<i32>, n: nat)
    requires n == s.len()
    requires forall|k: int| 0 <= k < ((n as int) - 1) ==> s@.index(k) >= s@.index(k+1)
    ensures forall|i: int, j: int| 0 <= i < j < (n as int) ==> s@.index(i) >= s@.index(j)
{
    if n <= 1 {
        return;
    }
    assert(forall|a: int, b: int| 0 <= a < b < (n as int) ==> s@.index(a) >= s@.index(b)) by {
        fix a, b;
        assume(0 <= a && a < b && b < (n as int));
        adj_ge_rec(s, n, a, b);
    };
    return;
}
// </vc-helpers>
```

```vc-code
{
    // impl-start
    let n = l.len();
    if n < 2 {
        // sequences of length 0 or 1 are