predicate ValidInput(n: int, m: int, k: int)
{
    1 <= n <= 10000 && 1 <= m <= 10000 && 1 <= k <= 2 * n * m
}

predicate ValidOutput(n: int, m: int, lane: int, desk: int, side: string)
{
    1 <= lane <= n && 1 <= desk <= m && (side == "L" || side == "R")
}

predicate CorrectSolution(n: int, m: int, k: int, lane: int, desk: int, side: string)
    requires ValidInput(n, m, k)
{
    lane == (k - 1) / (2 * m) + 1 &&
    desk == (k - 1) % (2 * m) / 2 + 1 &&
    (side == "L" <==> (k - 1) % (2 * m) % 2 == 0)
}

// <vc-helpers>
lemma Mod2Reduction(x: int, t: int)
    requires t > 0 && t % 2 == 0
    ensures x % 2 == (x % t) % 2
{
    var q := x / t;
    var r := x % t;
    assert x == q * t + r;
    var s := t / 2;
    assert t == 2 * s;
    assert q * t == 2 * (q * s);
    assert (q * t) % 2 == 0;
    assert x % 2 == (q * t + r) % 2;
    assert (q * t + r) % 2 == r % 2;
    assert r % 2 == (x % t) % 2;
}

lemma IndexBounds(n: int, m: int, k: int)
    requires ValidInput(n, m, k)
    ensures 0 <= k - 1
    ensures 0 <= (k - 1) % (2 * m) < 2 * m
    ensures 0 <= (k - 1) / (2 * m) <= n - 1
    ensures 0 <= (k - 1) % (2 * m) / 2 <= m - 1
{
    var idx := k - 1;
    var t := 2 * m;

    // idx >= 0
    assert idx >= 0;

    // r in [0, t)
    var r := idx % t;
    assert 0 <= r < t;

    // let q = idx / t, show 0 <= q <= n-1
    var q := idx / t;
    // q * t <= idx by division property
    assert q * t <= idx;
    // from k <= 2*n*m we get idx <= t*n - 1
    assert k <= 2 * n * m;
    assert idx <= 2 * n * m - 1;
    assert idx <= t * n - 1;
    // thus q * t <= t*n - 1, so q <= n - 1
    if q >= n {
        // derive contradiction: q * t >= n * t > t * n - 1
        assert q * t >= n * t;
        assert n * t == t * n;
        assert n * t > t * n - 1;
        assert q * t > t * n - 1;
        // but q * t <= idx <= t*n - 1 contradiction
        assert false;
    }
    assert 0 <= q <= n - 1;

    // for desk: s = r / 2, show 0 <= s <= m - 1
    var s := r / 2;
    assert 0 <= s;
    // r <= 2*m - 1 => s * 2 <= r <= 2*m - 1
    assert r <= 2 * m - 1;
    // if s >= m then s*2 >= m*2 = 2*m, contradict r <= 2*m -1
    if s >= m {
        assert s * 2 >= m * 2;
        assert m * 2 == 2 * m;
        assert s * 2 >= 2 * m;
        assert s * 2 > 2 * m - 1;
        assert false;
    }
    assert 0 <= s <= m - 1;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, k: int) returns (lane: int, desk: int, side: string)
    requires ValidInput(n, m, k)
    ensures ValidOutput(n, m, lane, desk, side)
    ensures CorrectSolution(n, m, k, lane, desk, side)
// </vc-spec>
// <vc-code>
{
    call IndexBounds(n, m, k);
    var idx := k - 1;
    var t := 2 * m;
    lane := idx / t + 1;
    desk := (idx % t) / 2 + 1;
    if idx % t % 2 == 0 {
        side := "L";
    } else {
        side := "R";
    }
    // assist parity reasoning (not strictly necessary but helps verifier)
    call Mod2Reduction(idx, t);
}
// </vc-code>

