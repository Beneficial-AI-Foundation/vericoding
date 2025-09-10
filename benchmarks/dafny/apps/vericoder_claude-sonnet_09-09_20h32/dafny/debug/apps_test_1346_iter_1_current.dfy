predicate ValidInput(n: int, m: int, p: int, f: seq<int>, g: seq<int>) {
    n >= 1 && m >= 1 &&
    p >= 2 &&
    |f| == n && |g| == m &&
    (forall k :: 0 <= k < |f| ==> f[k] > 0) &&
    (forall k :: 0 <= k < |g| ==> g[k] > 0) &&
    (exists k :: 0 <= k < |f| && f[k] % p != 0) &&
    (exists k :: 0 <= k < |g| && g[k] % p != 0)
}

predicate ValidResult(result: int, n: int, m: int, p: int, f: seq<int>, g: seq<int>) 
    requires p != 0
{
    exists i, j :: 0 <= i < |f| && 0 <= j < |g| &&
            (forall k :: 0 <= k < i ==> f[k] % p == 0) &&
            f[i] % p != 0 &&
            (forall k :: 0 <= k < j ==> g[k] % p == 0) &&
            g[j] % p != 0 &&
            result == i + j &&
            0 <= result < |f| + |g|
}

// <vc-helpers>
lemma ExistsNonDivisibleF(f: seq<int>, p: int)
    requires p != 0
    requires (exists k :: 0 <= k < |f| && f[k] % p != 0)
    ensures exists i :: 0 <= i < |f| && f[i] % p != 0 && (forall k :: 0 <= k < i ==> f[k] % p == 0)
{
    var S := set i | 0 <= i < |f| && f[i] % p != 0;
    assert S != {};
    var i := FindMinIndex(f, p);
    assert i in S;
    assert forall j :: j in S ==> i <= j;
    assert forall k :: 0 <= k < i ==> f[k] % p == 0;
}

lemma ExistsNonDivisibleG(g: seq<int>, p: int)
    requires p != 0
    requires (exists k :: 0 <= k < |g| && g[k] % p != 0)
    ensures exists j :: 0 <= j < |g| && g[j] % p != 0 && (forall k :: 0 <= k < j ==> g[k] % p == 0)
{
    var S := set j | 0 <= j < |g| && g[j] % p != 0;
    assert S != {};
    var j := FindMinIndexG(g, p);
    assert j in S;
    assert forall k :: k in S ==> j <= k;
    assert forall k :: 0 <= k < j ==> g[k] % p == 0;
}

function FindMinIndex(f: seq<int>, p: int): int
    requires p != 0
    requires |f| > 0
    requires exists k :: 0 <= k < |f| && f[k] % p != 0
    ensures 0 <= FindMinIndex(f, p) < |f|
    ensures f[FindMinIndex(f, p)] % p != 0
    ensures forall k :: 0 <= k < FindMinIndex(f, p) ==> f[k] % p == 0
{
    FindMinIndexHelper(f, p, 0)
}

function FindMinIndexG(g: seq<int>, p: int): int
    requires p != 0
    requires |g| > 0
    requires exists k :: 0 <= k < |g| && g[k] % p != 0
    ensures 0 <= FindMinIndexG(g, p) < |g|
    ensures g[FindMinIndexG(g, p)] % p != 0
    ensures forall k :: 0 <= k < FindMinIndexG(g, p) ==> g[k] % p == 0
{
    FindMinIndexHelperG(g, p, 0)
}

function FindMinIndexHelper(f: seq<int>, p: int, start: int): int
    requires p != 0
    requires 0 <= start < |f|
    requires exists k :: start <= k < |f| && f[k] % p != 0
    ensures start <= FindMinIndexHelper(f, p, start) < |f|
    ensures f[FindMinIndexHelper(f, p, start)] % p != 0
    ensures forall k :: start <= k < FindMinIndexHelper(f, p, start) ==> f[k] % p == 0
    decreases |f| - start
{
    if f[start] % p != 0 then start
    else FindMinIndexHelper(f, p, start + 1)
}

function FindMinIndexHelperG(g: seq<int>, p: int, start: int): int
    requires p != 0
    requires 0 <= start < |g|
    requires exists k :: start <= k < |g| && g[k] % p != 0
    ensures start <= FindMinIndexHelperG(g, p, start) < |g|
    ensures g[FindMinIndexHelperG(g, p, start)] % p != 0
    ensures forall k :: start <= k < FindMinIndexHelperG(g, p, start) ==> g[k] % p == 0
    decreases |g| - start
{
    if g[start] % p != 0 then start
    else FindMinIndexHelperG(g, p, start + 1)
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, p: int, f: seq<int>, g: seq<int>) returns (result: int)
    requires ValidInput(n, m, p, f, g)
    requires p != 0
    ensures ValidResult(result, n, m, p, f, g)
// </vc-spec>
// <vc-code>
{
    var i := 0;
    while i < |f| && f[i] % p == 0
        invariant 0 <= i <= |f|
        invariant forall k :: 0 <= k < i ==> f[k] % p == 0
    {
        i := i + 1;
    }
    
    var j := 0;
    while j < |g| && g[j] % p == 0
        invariant 0 <= j <= |g|
        invariant forall k :: 0 <= k < j ==> g[k] % p == 0
    {
        j := j + 1;
    }
    
    result := i + j;
}
// </vc-code>

