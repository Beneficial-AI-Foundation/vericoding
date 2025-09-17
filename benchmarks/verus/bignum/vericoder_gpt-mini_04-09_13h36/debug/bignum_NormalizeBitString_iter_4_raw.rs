```vc-helpers
proof fn lemma_drop_leading_zero(s: Seq<char>)
  requires ValidBitString(s)
  requires s.len() > 0
  requires s.index(0) == '0'
  ensures Str2Int(s) == Str2Int(s.subrange(1, s.len()))
  decreases s.len()
{
    if s.len() == 1 {
        // s = ['0']
        // Str2Int(s) = 2 * Str2Int(empty) + 0 = 0
        assert(Str2Int(s) == 0);
        assert(Str2Int(s.subrange(1, s.len())) == 0);
    } else {
        let n = s.len();
        let r = s.subrange(0, n - 1);
        assert(ValidBitString(r));
        assert(r.len() > 0);
        assert(r.index(0) == '0');
        lemma_drop_leading_zero(r);
        // Unfold Str2Int for s and for s.subrange(1,n)
        assert(Str2Int(s) == 2 * Str2Int(r) + (if s.index(n - 1) == '1' { 1 } else { 0 }));
        // The inner subrange of s.subrange(1,n) corresponds to r.subrange(1, r.len())
        assert(Str2Int(s.subrange(1, n)) ==
               2 * Str2Int(r.subrange(1, r.len())) + (if s.index(n - 1) == '1' { 1 } else { 0 }));
        // By induction on r
        assert(Str2Int(r) == Str2Int(r.subrange(1, r.len())));
        assert(2 * Str2Int(r) + (if s.index(n - 1) == '1' { 1 } else { 0 })
               == 2 * Str2Int(r.subrange(1, r.len())) + (if s.index(n - 1) == '1' { 1 } else { 0 }));
    }
}

proof fn lemma_drop_prefix_zeros(s: Seq<char>, k: int)
  requires ValidBitString(s)
  requires 0 <= k && k <= s.len()
  requires forall |i: int| 0 <= i && i < k ==> s.index(i) == '0'
  ensures Str2Int(s) == Str2Int(s.subrange(k, s.len()))
  decreases k
{
    if k == 0 {
        // trivial: subrange(0, s.len()) is s
    } else {
        // k > 0
        // first char is '0'
        assert(s.index(0) == '0');
        lemma_drop_leading_zero(s);
        // prepare s1 = s.subrange(1, s.len())
        let s1 = s.subrange(1, s.len());
        assert(ValidBitString(s1));
        // show prefix of length k-1 of s1 is all zeros
        // For any i with 0 <= i < k-1, s1.index(i) == s.index(i+1) and i+1 < k => s.index(i+1) == '0'
        assert(forall |i: int| 0 <= i && i < k - 1 ==>
            s1.index(i) == '0'
        ) by
        {
            |i: int|
            // assume 0 <= i && i < k-1
            // s1.index(i) equals s.index(i+1)
            assert(s1.index(i) == s.index(i + 1));
            // i+1 < k, so by precondition that index is '0'
            assert(s.index(i + 1) == '0');
            assert(s1.index(i) == '0');
        };
        lemma_drop_prefix_zeros(s1, k - 1);
    }
}
```

```vc-code
{
    let n_usize = s.len();
    let n: int = n_usize as int;

    // First pass: validate that s contains only '0' or '1'
    let mut i: int = 0;
    let mut ok: bool = true;
    while i < n
        invariant 0 <= i && i <= n
        invariant ok ==> (forall |j: int| 0 <= j && j < i ==> (s@.index(j) == '0' || s@.index(j) == '1'))
        decreases n - i
    {
        let c = s[i as usize];
        if c != '0' && c != '1' {
            ok = false;
        }
        i = i + 1;
    }

    if !ok {
        // Input not a valid bitstring: return canonical "0"
        let mut t = Vec::<char>::new();
        t.push('0');
        return t;
    }

    // Now s@ is ValidBitString
    // Second pass: find first '1'
    let mut first_one: int = 0;
    while first_one < n && s@.index(first_one) != '1'
        invariant 0 <= first_one && first_one <= n
        invariant forall |j: int| 0 <= j && j < first_one ==> s@.index(j) == '0'
        decreases n - first_one
    {
        first_one = first_one + 1;
    }

    if first_one == n {
        // All zeros -> return single '0'
        let mut t = Vec::<char>::new();
        t.push('0');
        proof {
            // All positions < n are '0'
            lemma_drop_prefix_zeros(s@, n);
            // Str2Int(s@) == Str2Int(s@.subrange(n, n)) == 0
            assert(Str2Int(s@) == Str2Int(s@.subrange(n, n)));
            assert(Str2Int(s@.subrange(n, n)) == 0);
            // Str2Int of t@ (single '0') is also 0
            assert(t@.len() == 1);
            assert(t@.index(0) == '0');
            assert(Str2Int(t@) == 2 * Str2Int(t@.subrange(0, 0)) + 0);
            assert(Str2Int(t@.subrange(0, 0)) == 0);
            assert(Str2Int(t@) == 0);
            // therefore equality holds
            assert(Str2Int(s@) == Str2Int(t@));
        }
        return t;
    }

    // Otherwise, construct t as s[first_one .. n)
    let mut t = Vec::<char>::new();
    let mut j: int = first_one;
    while j < n
        invariant first_one <= j && j <= n
        invariant t@ == s@.subrange(first_one, j)
        decreases n - j
    {
        let cc = s[j as usize];
        t.push(cc);
        j = j + 1;
    }

    // Now t@ == s@.subrange(first_one, n), and ValidBitString(t@) holds
    proof {
        lemma_drop_prefix_zeros(s@, first_one);
        assert(Str2Int(s@) == Str2Int(s@.subrange(first_one, n)));
        assert(t@ == s@.subrange(first_one, n));
        assert(Str2Int(s@) == Str2Int(t@));
    }

    return t;
}
```