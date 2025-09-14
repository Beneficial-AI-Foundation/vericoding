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
lemma FirstNonDivisibleExists(s: seq<int>, p: int) returns (index: int)
    requires p != 0
    requires |s| > 0
    requires forall k :: 0 <= k < |s| ==> s[k] > 0
    requires exists k :: 0 <= k < |s| && s[k] % p != 0
    ensures 0 <= index < |s|
    ensures s[index] % p != 0
    ensures forall k :: 0 <= k < index ==> s[k] % p == 0
{
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall k :: 0 <= k < i ==> s[k] % p == 0
        decreases |s| - i
    {
        if s[i] % p != 0 {
            index := i;
            return;
        }
        i := i + 1;
    }
    // This point should be unreachable due to the precondition
    assert false;
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
    while i < |f|
        invariant 0 <= i <= |f|
        invariant forall k :: 0 <= k < i ==> f[k] % p == 0
        decreases |f| - i
    {
        if f[i] % p != 0 {
            break;
        }
        i := i + 1;
    }
    
    var j := 0;
    while j < |g|
        invariant 0 <= j <= |g|
        invariant forall k :: 0 <= k < j ==> g[k] % p == 0
        decreases |g| - j
    {
        if g[j] % p != 0 {
            break;
        }
        j := j + 1;
    }
    
    result := i + j;
}
// </vc-code>

