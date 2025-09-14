// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function method MaxInt(a: int, b: int): int { if a < b then b else a }
predicate IsPrefixMax(a: array<int>, x: nat, m: int) reads a { x <= a.Length && (forall i :: 0 <= i < x ==> a[i] <= m) && (x > 0 ==> (exists i :: 0 <= i < x && a[i] == m)) }
lemma Lemma_FirstGreaterWitness(a: array<int>, x: nat, p: nat, m: int)
  requires a != null && x <= p < a.Length && a[p] > m
  ensures exists i :: x <= i <= p && a[i] > m
  reads a
{
}

// </vc-helpers>

// <vc-spec>
method OnlineMax(a: array<int>, x: int) returns (result: (int, int))
    requires
        a.Length > 0 &&
        x < a.Length
    ensures
        var (m, p) := result;
        x <= p && p < a.Length &&
        (forall i :: 0 <= i < x ==> a[i] <= m) &&
        (exists i :: 0 <= i < x && a[i] == m) &&
        ((p < a.Length - 1) ==> (exists i :: x <= i <= p && a[i] > m)) &&
        ((forall i :: x <= i < a.Length ==> a[i] <= m) ==> p == a.Length - 1)
// </vc-spec>
// <vc-code>
{
  var m: int;
  var idx: int;
  m := a[0];
  idx := 0;
  if x > 0 {
    m := a[0];
    idx := 0;
    var i := 1;
    while i < x
      invariant 1 <= i <= x
      invariant 0 <= idx < i
      invariant forall j :: 0 <= j < i ==> a[j] <= m
      invariant a[idx] == m
    {
      if a[i] > m {
        m := a[i];
        idx := i;
      }
      i := i + 1;
    }
  } else {
    m := a[0];
    idx := 0;
  }
  var p: int;
  var found := false;
  p := a.Length - 1;
  var j := x;
  while j < a.Length
    invariant x <= j <= a.Length
    invariant (!found ==> forall k :: x <= k < j ==> a[k] <= m)
    invariant (found ==> x <= p < j && a[p] > m && forall k :: x <= k < p ==> a[k] <= m)
  {
    if a[j] > m && !found {
      found := true;
      p := j;
    }
    j := j + 1;
  }
  if !found {
    p := a.Length - 1;
  }
  result := (m, p);
}

// </vc-code>
