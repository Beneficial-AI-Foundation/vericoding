

// <vc-helpers>
lemma ChainStrictIncrease(xs: seq<int>, i: int, j: int)
  requires 0 <= i < j < |xs|
  requires forall k :: 0 <= k < |xs| - 1 ==> xs[k] < xs[k+1]
  ensures xs[i] < xs[j]
  decreases j - i
{
  if i + 1 == j {
    // direct adjacent comparison
    assert xs[i] < xs[j];
    return;
  }
  // prove xs[i] < xs[j-1]
  ChainStrictIncrease(xs, i, j - 1);
  // and xs[j-1] < xs[j] from global adjacent assumption
  assert xs[j-1] < xs[j];
  // transitivity
  assert xs[i] < xs[j];
}

lemma ChainStrictDecrease(xs: seq<int>, i: int, j: int)
  requires 0 <= i < j < |xs|
  requires forall k :: 0 <= k < |xs| - 1 ==> xs[k] > xs[k+1]
  ensures xs[i] > xs[j]
  decreases j - i
{
  if i + 1 == j {
    assert xs[i] > xs[j];
    return;
  }
  ChainStrictDecrease(xs, i, j - 1);
  assert xs[j-1] > xs[j];
  assert xs[i] > xs[j];
}

lemma AdjacentImpliesAllIncreasing(xs: seq<int>)
  requires |xs| > 0
  requires forall k :: 0 <= k < |xs| - 1 ==> xs[k] < xs[k+1]
  ensures forall i, j :: 0 <= i < j < |xs| ==> xs[i] < xs[j]
{
  var n := |xs|;
  var i := 0;
  while i < n
    decreases n - i
    invariant 0 <= i <= n
    invariant forall p, q :: 0 <= p < q < n && p < i ==> xs[p] < xs[q]
  {
    var j := i + 1;
    while j < n
      decreases n - j
      invariant i + 1 <= j <= n
      invariant forall q :: 0 <= i < q < j ==> xs[i] < xs[q]
    {
      ChainStrictIncrease(xs, i, j);
      // after ChainStrictIncrease we have xs[i] < xs[j], so the inner invariant
      // will hold for the next j when we increment.
      j := j + 1;
    }
    // After the inner loop, for all q > i we have xs[i] < xs[q], so the outer invariant
    // will hold for i+1.
    i := i + 1;
  }
}

lemma AdjacentImpliesAllDecreasing(xs: seq<int>)
  requires |xs| > 0
  requires forall k :: 0 <= k < |xs| - 1 ==> xs[k] > xs[k+1]
  ensures forall i, j :: 0 <= i < j < |xs| ==> xs[i] > xs[j]
{
  var n := |xs|;
  var i := 0;
  while i < n
    decreases n - i
    invariant 0 <= i <= n
    invariant forall p, q :: 0 <= p < q < n && p < i ==> xs[p] > xs[q]
  {
    var j := i + 1;
    while j < n
      decreases n - j
      invariant i + 1 <= j <= n
      invariant forall q :: 0 <= i < q < j ==> xs[i] > xs[q]
    {
      ChainStrictDecrease(xs, i, j);
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method monotonic(xs: seq<int>) returns (result: bool)
  // pre-conditions-start
  requires |xs| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures result <==> (forall i, j :: 0 <= i < j < |xs| ==> xs[i] < xs[j]) || (forall i, j :: 0 <= i < j < |xs| ==> xs[i] > xs[j])
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var n := |xs|;
  var incFlag := forall k :: 0 <= k < n - 1 ==> xs[k] < xs[k+1];
  var decFlag := forall k :: 0 <= k < n - 1 ==> xs[k] > xs[k+1];
  result := incFlag || decFlag;

  // If result holds, show global pairwise monotonicity
  if result {
    if incFlag {
      AdjacentImpliesAllIncreasing(xs);
    } else {
      AdjacentImpliesAllDecreasing(xs);
    }
  }

  // If global strictly increasing holds, then adjacent increasing holds, hence result
  if forall i, j :: 0 <= i < j < n ==> xs[i] < xs[j] {
    assert forall k :: 0 <= k < n - 1 ==> xs[k] < xs[k+1];
    assert incFlag;
    assert result;
  }

  // If global strictly decreasing holds, then adjacent decreasing holds, hence result
  if forall i, j :: 0 <= i < j < n ==> xs[i] > xs[j] {
    assert forall k :: 0 <= k < n - 1 ==> xs[k] > xs[k+1];
    assert decFlag;
    assert result;
  }
}
// </vc-code>

