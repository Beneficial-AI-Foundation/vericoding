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
predicate ValidInput(n: int, a: seq<int>, p: string)
{
    n >= 2 &&
    |a| == n &&
    |p| == n - 1 &&
    (forall i :: 0 <= i < |p| ==> p[i] == '0' || p[i] == '1') &&
    (forall i :: 0 <= i < |a| ==> 1 <= a[i] <= n) &&
    (forall i {:trigger a[j]} :: 1 <= i <= n ==> exists j :: 0 <= j < |a| && a[j] == i)
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

// Additional lemma to help with verification
lemma MaxUpToDef(a: seq<int>, i: int)
    requires 0 <= i < |a|
    ensures forall j :: 0 <= j <= i ==> a[j] <= max_up_to(a, i)
    ensures max_up_to(a, i) == a[i] || max_up_to(a, i) == max_up_to(a, i-1)
{
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
    var current_max := if |a| > 0 then a[0] else 0;
    while i < n - 1
        invariant 0 <= i <= n - 1
        invariant can <==> forall k :: 0 <= k < i ==> !(p[k] == '0' && max_up_to(a, k) > k + 1)
        invariant current_max == if i == 0 then (if |a| > 0 then a[0] else 0) else max_up_to(a, i - 1)
    {
        var m := if i == 0 then a[0] else if a[i] > current_max then a[i] else current_max;
        if p[i] == '0' && !(m <= i + 1) {
            can := false;
        }
        current_max := m;
        i := i + 1;
    }
    result := if can then "YES" else "NO";
}
// </vc-code>

