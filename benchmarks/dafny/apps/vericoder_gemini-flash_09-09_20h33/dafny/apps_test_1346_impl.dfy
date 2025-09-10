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
function find_first_non_multiple(s: seq<int>, p: int): (index: int)
    requires p != 0
    requires (exists k :: 0 <= k < |s| && s[k] % p != 0)
    ensures 0 <= index < |s|
    ensures s[index] % p != 0
    ensures forall k :: 0 <= k < index ==> s[k] % p == 0
{
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall k :: 0 <= k < i ==> s[k] % p == 0
        invariant exists k_nmi :: i <= k_nmi < |s| && s[k_nmi] % p != 0
        decreases |s| - i
    {
        if s[i] % p != 0 {
            return i;
        }
        i := i + 1;
    }
    // This part should not be reachable due to the precondition
    // but Dafny requires an explicit return statement.
    // The loop invariant 'exists k_nmi :: i <= k_nmi < |s| && s[k_nmi] % p != 0'
    // along with the loop condition 'i < |s|' ensures that a non-multiple element will be found
    // before 'i' reaches '|s|', making this unreachable.
    return 0; // This return is formally unreachable given the postcondition
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
    var i := find_first_non_multiple(f, p);
    var j := find_first_non_multiple(g, p);
    result := i + j;
}
// </vc-code>

