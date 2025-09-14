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
lemma ZeroIndexedArrayAllBounds(n: int, f: seq<int>)
    requires ValidInput(n, f)
    ensures forall k :: 0 <= k < n ==> 0 <= ZeroIndexedArray(n, f)[k] < n
{
  var k := 0;
  while k < n
    invariant 0 <= k <= n
    invariant forall j :: 0 <= j < k ==> 0 <= ZeroIndexedArray(n, f)[j] < n
  {
    assert 1 <= f[k] && f[k] <= n;
    assert ZeroIndexedArray(n, f)[k] == f[k] - 1;
    assert 0 <= ZeroIndexedArray(n, f)[k] < n;
    k := k + 1;
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
  ZeroIndexedArrayAllBounds(n, f);
  var i := 0;
  var found := false;
  while i < n
    invariant 0 <= i <= n
    invariant found <==> exists j :: 0 <= j < i && a[a[a[j]]] == j
  {
    if a[a[a[i]]] == i {
      found := true;
    }
    i := i + 1;
  }
  if found {
    return "YES";
  } else {
    return "NO";
  }
}
// </vc-code>

