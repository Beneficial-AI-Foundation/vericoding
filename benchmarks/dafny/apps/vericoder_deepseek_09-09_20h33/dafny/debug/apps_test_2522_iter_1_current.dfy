predicate ValidInput(n: int, a: seq<int>, b: seq<int>)
{
    |a| == n && |b| == n && n >= 1 &&
    (forall i :: 0 <= i < n-1 ==> a[i] <= a[i+1]) &&
    (forall i :: 0 <= i < n-1 ==> b[i] <= b[i+1])
}

predicate ValidReordering(a: seq<int>, reordered_b: seq<int>)
    requires |a| == |reordered_b|
{
    forall i :: 0 <= i < |a| ==> a[i] != reordered_b[i]
}

predicate IsReorderingOf(original: seq<int>, reordered: seq<int>)
{
    |original| == |reordered| && multiset(original) == multiset(reordered)
}

predicate IsRotation(original: seq<int>, rotated: seq<int>)
{
    |original| == |rotated| && 
    (exists k :: 0 <= k < |original| && rotated == original[k..] + original[..k])
}

// <vc-helpers>
lemma LemmaRotatedIsReordering(original: seq<int>, rotated: seq<int>)
  requires |original| == |rotated| && IsRotation(original, rotated)
  ensures IsReorderingOf(original, rotated)
{
  var k :| 0 <= k < |original| && rotated == original[k..] + original[..k];
  var s1 := original[k..];
  var s2 := original[..k];
  calc {
    multiset(rotated);
    ==
    multiset(original[k..] + original[..k]);
    ==
    multiset(original[k..]) + multiset(original[..k]);
    ==
    multiset(original);
  }
}

lemma LemmaRotationValidReordering(a: seq<int>, rotated: seq<int>)
  requires |a| == |rotated| && IsRotation(a, rotated)
  ensures ValidReordering(a, rotated)
{
  var k :| 0 <= k < |a| && rotated == a[k..] + a[..k];
  if k == 0 {
    assert rotated == a;
    forall i | 0 <= i < |a|
      ensures a[i] != rotated[i]
    {
      assert rotated[i] == a[i];
    }
  } else {
    forall i | 0 <= i < |a|
      ensures a[i] != rotated[i]
    {
      if i < |a| - k {
        assert rotated[i] == a[k + i];
        assert a[i] <= a[k + i];
        if a[i] == a[k + i] {
          assert false; // Contradicts sortedness and k != 0
        }
      } else {
        assert rotated[i] == a[i - (|a| - k)];
        assert a[i - (|a| - k)] <= a[i];
        if a[i - (|a| - k)] == a[i] {
          assert false; // Contradicts sortedness and k != 0
        }
      }
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>, b: seq<int>) returns (result: (bool, seq<int>))
    requires ValidInput(n, a, b)
    ensures result.0 ==> |result.1| == n
    ensures result.0 ==> IsReorderingOf(b, result.1)
    ensures result.0 ==> ValidReordering(a, result.1)
    ensures !result.0 ==> result.1 == []
    ensures result.0 ==> IsRotation(b, result.1)
// </vc-spec>
// <vc-code>
{
  var k := 0;
  while k < n
    invariant 0 <= k <= n
  {
    var rotated := b[k..] + b[..k];
    if ValidReordering(a, rotated) {
      return (true, rotated);
    }
    k := k + 1;
  }
  return (false, []);
}
// </vc-code>

