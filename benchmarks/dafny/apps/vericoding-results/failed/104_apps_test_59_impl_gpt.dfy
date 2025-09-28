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
method CanSortCompute(n: int, a: seq<int>, p: string) returns (b: bool)
  requires ValidInput(n, a, p)
  ensures b <==> CanSort(n, a, p)
{
  var i := 0;
  var m := a[0];
  var ok := true;
  while i < n - 1
    invariant 0 <= i <= n - 1
    invariant m == max_up_to(a, i)
    invariant ok == (forall k :: 0 <= k < i ==> (p[k] == '0' ==> max_up_to(a, k) <= k + 1))
    decreases n - 1 - i
  {
    ok := ok && (p[i] != '0' || m <= i + 1);
    i := i + 1;
    if a[i] > m {
      m := a[i];
    }
  }
  b := ok;
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
  var b := CanSortCompute(n, a, p);
  if b {
    result := "YES";
  } else {
    result := "NO";
  }
}
// </vc-code>

