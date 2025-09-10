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
lemma LoveTriangleExists(n: int, f: seq<int>) returns (found: bool, witness: int)
    requires ValidInput(n, f)
    ensures found <==> HasLoveTriangle(n, f)
    ensures found ==> 0 <= witness < n
    ensures found ==> 
        var a := ZeroIndexedArray(n, f);
        0 <= a[witness] < n && 0 <= a[a[witness]] < n && a[a[a[witness]]] == witness
{
    var a := ZeroIndexedArray(n, f);
    found := false;
    witness := 0;
    
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant !found ==> forall k :: 0 <= k < i ==> !(0 <= a[k] < n && 0 <= a[a[k]] < n && a[a[a[k]]] == k)
        invariant found ==> 0 <= witness < n && 0 <= a[witness] < n && 0 <= a[a[witness]] < n && a[a[a[witness]]] == witness
    {
        if 0 <= a[i] < n && 0 <= a[a[i]] < n && a[a[a[i]]] == i {
            found := true;
            witness := i;
            return;
        }
        i := i + 1;
    }
    
    if found {
        assert HasLoveTriangleWith(n, a);
    } else {
        assert !HasLoveTriangleWith(n, a);
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
    var found, witness := LoveTriangleExists(n, f);
    if found {
        result := "YES";
    } else {
        result := "NO";
    }
}
// </vc-code>

