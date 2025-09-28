predicate ValidInput(n: int, a: seq<int>, p: string)
{
    n >= 2 &&
    |a| == n &&
    |p| == n - 1 &&
    (forall i :: 0 <= i < |p| ==> p[i] == '0' || p[i] == '1') &&
    (forall i :: 0 <= i < |a| ==> 1 <= a[i] <= n) &&
    (forall i :: 1 <= i <= n ==> exists j :: 0 <= j < |a| && a[j] == i)
}

function max_up_to(a: seq<int>, i: int): int
    requires 0 <= i < |a|
    decreases i
{
    if i == 0 then a[0]
    else if a[i] > max_up_to(a, i-1) then a[i]
    else max_up_to(a, i-1)
}

predicate CanSort(n: int, a: seq<int>, p: string)
    requires ValidInput(n, a, p)
{
    forall i :: 0 <= i < n - 1 ==> 
        (p[i] == '0' ==> max_up_to(a, i) <= i + 1)
}

// <vc-helpers>
// Additional lemma to help with verification
lemma MaxUpToDef(a: seq<int>, i: int)
    requires 0 <= i < |a|
    ensures forall j {:trigger max_up_to(a, j)} :: 0 <= j <= i ==> a[j] <= max_up_to(a, i)
{
    var m := max_up_to(a, i);
    if i == 0 {
        assert a[0] <= a[0];
        assert forall j :: 0 <= j <= 0 ==> a[j] <= max_up_to(a, 0);
    } else {
        MaxUpToDef(a, i-1);
        var prev := max_up_to(a, i-1);
        assert forall j :: 0 <= j <= i-1 ==> a[j] <= prev;
        assert m == if a[i] > prev then a[i] else prev;
        assert a[i] <= m;
        assert forall j :: 0 <= j <= i ==> if j <= i-1 then a[j] <= prev <= m else a[j] <= m;
    }
}

// Fixed ValidInput with trigger
predicate ValidInput(n: int, a: seq<int>, p: string)
{
    n >= 2 &&
    |a| == n &&
    |p| == n - 1 &&
    (forall i :: 0 <= i < |p| ==> p[i] == '0' || p[i] == '1') &&
    (forall i :: 0 <= i < |a| ==> 1 <= a[i] <= n) &&
    (forall i :: 1 <= i <= n ==> exists j {:trigger a[j]} :: 0 <= j < |a| && a[j] == i)
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>, p: string) returns (result: string)
    requires ValidInput(n, a, p)
    ensures result == "YES" || result == "NO"
    ensures result == "YES" <==> CanSort(n, a, p)
// </vc-spec>
// <vc-code>
{
    var can := true;
    var i := 0;
    while i < n - 1
        invariant 0 <= i <= n - 1
        invariant can <==> forall k {:trigger max_up_to(a, k)} :: 0 <= k < i ==> (p[k] != '0' || max_up_to(a, k) <= k + 1)
    {
        var m := max_up_to(a, i);
        if p[i] == '0' && m > i + 1 {
            can := false;
        }
        i := i + 1;
    }
    result := if can then "YES" else "NO";
}
// </vc-code>

