predicate ValidInput(n: int, f: seq<int>)
{
    n >= 2 && n <= 5000 &&
    |f| == n &&
    forall i :: 0 <= i < |f| ==> 1 <= f[i] <= n && f[i] != i + 1
}

function ZeroIndexedArray(n: int, f: seq<int>): seq<int>
    requires ValidInput(n, f)
{
    seq(n, j requires 0 <= j < n => f[j] - 1)
}

predicate HasLoveTriangleWith(n: int, a: seq<int>)
    requires |a| == n
    requires forall k :: 0 <= k < n ==> 0 <= a[k] < n
{
    exists i {:trigger a[i], a[a[i]], a[a[a[i]]]} :: 0 <= i < n && 
        0 <= a[i] < n && 0 <= a[a[i]] < n && a[a[a[i]]] == i
}

predicate HasLoveTriangle(n: int, f: seq<int>)
    requires ValidInput(n, f)
{
    var a := ZeroIndexedArray(n, f);
    HasLoveTriangleWith(n, a)
}

// <vc-helpers>
lemma ZeroIndexedArrayProperties(n: int, f: seq<int>)
    requires ValidInput(n, f)
    ensures var a := ZeroIndexedArray(n, f);
            |a| == n &&
            forall k :: 0 <= k < n ==> 0 <= a[k] < n && a[k] == f[k] - 1
{
    var a := ZeroIndexedArray(n, f);
    assert |a| == n;
    forall k | 0 <= k < n
        ensures 0 <= a[k] < n && a[k] == f[k] - 1
    {
        assert a[k] == f[k] - 1;
        assert 1 <= f[k] <= n;
        assert 0 <= f[k] - 1 < n;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, f: seq<int>) returns (result: string)
    requires ValidInput(n, f)
    ensures result == "YES" || result == "NO"
    ensures result == "YES" <==> HasLoveTriangle(n, f)
// </vc-spec>
// <vc-code>
{
    var a := ZeroIndexedArray(n, f);
    ZeroIndexedArrayProperties(n, f);
    
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall j :: 0 <= j < i ==> !(0 <= a[j] < n && 0 <= a[a[j]] < n && a[a[a[j]]] == j)
        invariant !exists j :: 0 <= j < i && 0 <= a[j] < n && 0 <= a[a[j]] < n && a[a[a[j]]] == j
    {
        if a[i] < n && a[a[i]] < n && a[a[a[i]]] == i {
            return "YES";
        }
        i := i + 1;
    }
    
    return "NO";
}
// </vc-code>

