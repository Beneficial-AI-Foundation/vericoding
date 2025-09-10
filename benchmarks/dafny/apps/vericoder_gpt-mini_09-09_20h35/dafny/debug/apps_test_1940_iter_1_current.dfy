predicate ValidInput(n: int, k: int, w: seq<int>)
{
    k > 0 && n >= 0 && |w| == n && forall i :: 0 <= i < |w| ==> w[i] >= 0
}

function sum_trips(w: seq<int>, k: int): int
    requires k > 0
    requires forall i :: 0 <= i < |w| ==> w[i] >= 0
    ensures sum_trips(w, k) >= 0
{
    if |w| == 0 then 0
    else (w[0] + k - 1) / k + sum_trips(w[1..], k)
}

// <vc-helpers>
lemma SumTripsAppendElem(a: seq<int>, x: int, k: int)
  requires k > 0
  requires forall i :: 0 <= i < |a| ==> a[i] >= 0
  requires x >= 0
  ensures sum_trips(a + [x], k) == sum_trips(a, k) + (x + k - 1) / k
  decreases |a|
{
  if |a| == 0 {
    // sum_trips([x],k) == (x+k-1)/k and sum_trips([],k) == 0 by definition
  } else {
    SumTripsAppendElem(a[1..], x, k);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, w: seq<int>) returns (result: int)
    requires ValidInput(n, k, w)
    ensures result >= 0
    ensures result == (sum_trips(w, k) + 1) / 2
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var s := 0;
  while i < n
    invariant 0 <= i <= n
    invariant s == sum_trips(w[..i], k)
  {
    SumTripsAppendElem(w[..i], w[i], k);
    s := s + (w[i] + k - 1) / k;
    i := i + 1;
  }
  result := (s + 1) / 2;
}
// </vc-code>

