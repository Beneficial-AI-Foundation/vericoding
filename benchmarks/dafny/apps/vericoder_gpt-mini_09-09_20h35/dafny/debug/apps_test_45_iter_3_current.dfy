predicate ValidInput(n: int, k: int)
{
    n > 0 && k > 0
}

predicate IsStrictlyIncreasing(s: seq<int>)
{
    forall i :: 0 <= i < |s| - 1 ==> s[i] < s[i+1]
}

predicate AllPositive(s: seq<int>)
{
    forall i :: 0 <= i < |s| ==> s[i] > 0
}

function sum(s: seq<int>): int
    decreases |s|
{
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}

predicate ValidSequence(s: seq<int>, n: int, k: int)
{
    |s| == k && AllPositive(s) && IsStrictlyIncreasing(s) && sum(s) == n
}

predicate IsPossible(n: int, k: int)
{
    k * (k + 1) / 2 <= n
}

// <vc-helpers>
lemma SumAppend(s: seq<int>, x: int)
  ensures sum(s + [x]) == sum(s) + x
  decreases |s|
{
  if |s| == 0 {
    // sum([x]) == 0 + x by definition of sum
  } else {
    // sum(s + [x]) == s[0] + sum(s[1..] + [x])
    SumAppend(s[1..], x);
    // then sum(s + [x]) == s[0] + (sum(s[1..]) + x) == sum(s) + x
  }
}

lemma SumFirstK(k: int, s: seq<int>)
  requires k >= 0
  requires |s| == k
  requires forall i :: 0 <= i < k ==> s[i] == i + 1
  ensures sum(s) == k * (k + 1) / 2
  decreases k
{
  if k == 0 {
    // sum([]) == 0
  } else {
    // s[0] == 1 and s[1..] satisfies the same pattern for k-1
    SumFirstK(k - 1, s[1..]);
    // sum(s) == s[0] + sum(s[1..]) == 1 + (k-1)*k/2 == k*(k+1)/2
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: seq<int>)
    requires ValidInput(n, k)
    ensures (|result| == 1 && result[0] == -1) || 
            (ValidSequence(result, n, k))
    ensures (|result| == 1 && result[0] == -1) <==> !IsPossible(n, k)
// </vc-spec>
// <vc-code>
{
  if !IsPossible(n, k) {
    return [-1];
  }

  var res: seq<int> := [];
  var ssum: int := 0;
  var i := 1;
  while i <= k
    invariant 1 <= i <= k + 1
    invariant |res| == i - 1
    invariant sum(res) == ssum
    invariant forall j :: 0 <= j < |res| ==> res[j] == j + 1
  {
    var prev := res;
    res := prev + [i];
    ssum := ssum + i;
    SumAppend(prev, i);
    // prove the element property for the new res
    assert forall j :: 0 <= j < |res| ==> res[j] == j + 1 by {
      take j;
      if j < |prev| {
        assert res[j] == prev[j];
        assert prev[j] == j + 1;
      } else {
        // j == |prev| and |prev| == i - 1
        assert j == |prev|;
        assert res[j] == i;
        assert i == j + 1;
      }
    }
    // sum(res) == ssum follows from SumAppend(prev, i) and previous invariant
    assert sum(res) == ssum;
    i := i + 1;
  }

  // Now res == [1,2,...,k] and ssum == sum(res) == k*(k+1)/2
  SumFirstK(k, res);
  assert ssum == k * (k + 1) / 2;

  var rem := n - ssum;
  // From IsPossible and the above equality, rem >= 0
  assert rem >= 0;

  if k == 0 {
    // should not happen due to ValidInput, but handle defensively
    return [-1];
  }

  var pref := res[..|res|-1];
  var last := res[|res|-1];
  var newLast := last + rem;
  // build the final sequence
  var final := pref + [newLast];
  // relate sums
  SumAppend(pref, last);
  assert sum(res) == sum(pref) + last;
  SumAppend(pref, newLast);
  assert sum(final) == sum(pref) + newLast;
  assert sum(final) == sum(res) - last + newLast;
  assert sum(final) == ssum + rem;
  assert sum(final) == n;

  // prove strictly increasing:
  assert forall j :: 0 <= j < |final| - 1 ==> final[j] < final[j+1] by {
    take j;
    if j < |final| - 2 {
      // both entries are from the prefix: final[j] == j+1 and final[j+1] == j+2
      assert final[j] == j + 1;
      assert final[j+1] == j + 2;
      assert final[j] < final[j+1];
    } else {
      // j == |final|-2 : compare the penultimate (k-1) with last (k + rem)
      assert j == |final| - 2;
      // penultimate equals (k-1)
      assert final[j] == j + 1;
      assert final[j+1] == newLast;
      // j+1 == k-1 + 1 == k, and newLast == k + rem, rem >= 0
      assert final[j] < final[j+1];
    }
  }

  // prove all positive
  assert forall j :: 0 <= j < |final| ==> final[j] > 0 by {
    take j;
    if j < |final| - 1 {
      // final[j] == j+1 >= 1
      assert final[j] == j + 1;
      assert final[j] > 0;
    } else {
      // last element is newLast = k + rem >= 1
      assert final[j] == newLast;
      assert newLast >= k;
      assert k > 0;
      assert final[j] > 0;
    }
  }

  return final;
}
// </vc-code>

