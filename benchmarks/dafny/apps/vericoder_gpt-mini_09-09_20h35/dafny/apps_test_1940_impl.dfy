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
    // sum_trips([x],k) == (x+k-1)/k + sum_trips([],k) and sum_trips([],k) == 0
    assert sum_trips([x], k) == (x + k - 1) / k + sum_trips([], k);
    assert sum_trips([], k) == 0;
    assert sum_trips([x], k) == sum_trips([], k) + (x + k - 1) / k;
  } else {
    // Use induction on tail
    SumTripsAppendElem(a[1..], x, k);
    // Unfold definitions and restructure
    assert sum_trips(a + [x], k) == (a[0] + k - 1) / k + sum_trips((a + [x])[1..], k);
    // sequence slicing identity: (a + [x])[1..] == a[1..] + [x]
    assert (a + [x])[1..] == a[1..] + [x];
    assert sum_trips((a + [x])[1..], k) == sum_trips(a[1..] + [x], k);
    assert sum_trips(a[1..] + [x], k) == sum_trips(a[1..], k) + (x + k - 1) / k;
    assert (a[0] + k - 1) / k + sum_trips(a[1..], k) == sum_trips(a, k);
    calc {
      sum_trips(a + [x], k);
      == (a[0] + k - 1) / k + sum_trips((a + [x])[1..], k);
      == (a[0] + k - 1) / k + sum_trips(a[1..] + [x], k);
      == (a[0] + k - 1) / k + sum_trips(a[1..], k) + (x + k - 1) / k;
      == sum_trips(a, k) + (x + k - 1) / k;
    }
  }
}

lemma ElemNonneg(w: seq<int>, i: int)
  requires 0 <= i < |w|
  requires forall j :: 0 <= j < |w| ==> w[j] >= 0
  ensures w[i] >= 0
{
  // instantiate the universal quantifier
  assert w[i] >= 0;
}

lemma PrefixNonneg(w: seq<int>, i: int)
  requires 0 <= i <= |w|
  requires forall j :: 0 <= j < |w| ==> w[j] >= 0
  ensures forall j :: 0 <= j < |w[..i]| ==> w[..i][j] >= 0
{
  var j := 0;
  while j < |w[..i]|
    invariant 0 <= j <= |w[..i]|
    invariant forall t :: 0 <= t < j ==> w[..i][t] >= 0
  {
    // w[..i][j] == w[j] and j < i <= |w|, so w[j] >= 0
    assert w[..i][j] == w[j];
    assert 0 <= j < |w|;
    assert w[j] >= 0;
    j := j + 1;
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
    var oldi := i;
    var olds := s;
    // Prove that the prefix w[..oldi] has non-negative elements
    PrefixNonneg(w, oldi);
    // Prove the current element is non-negative
    ElemNonneg(w, oldi);
    var added := (w[oldi] + k - 1) / k;
    // Use lemma to update sum_trips for appended element
    SumTripsAppendElem(w[..oldi], w[oldi], k);
    // Relate the appended prefix to the next prefix
    assert w[..oldi] + [w[oldi]] == w[..oldi + 1];
    assert sum_trips(w[..oldi + 1], k) == sum_trips(w[..oldi], k) + added;
    i := oldi + 1;
    s := olds + added;
    // restore invariant explicitly
    assert s == sum_trips(w[..i], k);
  }
  // At loop exit i == n and invariant gives s == sum_trips(w[..i],k)
  assert i == n;
  assert s == sum_trips(w[..i], k);
  // From precondition ValidInput we have |w| == n, so w[..i] == w
  assert |w| == n;
  assert i == |w|;
  assert w[..i] == w;
  assert sum_trips(w[..i], k) == sum_trips(w, k);
  assert s == sum_trips(w, k);
  result := (s + 1) / 2;
}
// </vc-code>

