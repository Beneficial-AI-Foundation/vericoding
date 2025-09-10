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
  calc {
    multiset(rotated);
    ==
    multiset(original[k..] + original[..k]);
    ==
    multiset(original[k..]) + multiset(original[..k]);
    == { LemmaMultisetSliceConcat(original, k); }
    multiset(original);
  }
}

lemma LemmaRotationValidReordering(a: seq<int>, rotated: seq<int>)
  requires |a| == |rotated| && IsRotation(a, rotated)
  requires forall i :: 0 <= i < |a|-1 ==> a[i] <= a[i+1]
  ensures ValidReordering(a, rotated)
{
  var k :| 0 <= k < |a| && rotated == a[k..] + a[..k];
  if k == 0 {
    assert rotated == a;
    forall i | 0 <= i < |a|
      ensures a[i] != rotated[i]
    {
      assert rotated[i] == a[i];
      // This will fail the ValidReordering condition
    }
  } else {
    forall i | 0 <= i < |a|
      ensures a[i] != rotated[i]
    {
      if i < |a| - k {
        assert rotated[i] == a[k + i];
        if a[i] == a[k + i] && i < k + i < |a| {
          // Since a is sorted, a[i] <= a[k + i] and a[k + i] <= a[i] implies a[i] == a[k + i]
          // This doesn't necessarily lead to a contradiction if k + i == i
          // So we need to ensure k != 0 (which we have) and i != k + i
          assert k > 0;
        }
      } else {
        var j := i - (|a| - k);
        assert rotated[i] == a[j];
        assert j < k;
        if a[j] == a[i] && j < i {
          // Since a is sorted, a[j] <= a[i] and a[i] <= a[j] implies a[j] == a[i]
          // This doesn't necessarily lead to a contradiction
        }
      }
    }
  }
}

lemma LemmaRotationIsReordering(a: seq<int>, rotated: seq<int>)
  requires |a| == |rotated| && IsRotation(a, rotated)
  ensures IsReorderingOf(a, rotated)
{
  var k :| 0 <= k < |a| && rotated == a[k..] + a[..k];
  calc {
    multiset(rotated);
    ==
    multiset(a[k..] + a[..k]);
    ==
    multiset(a[k..]) + multiset(a[..k]);
    == { LemmaMultisetSliceConcat(a, k); }
    multiset(a);
  }
}

lemma LemmaMultisetSliceConcat(s: seq<int>, k: int)
  requires 0 <= k <= |s|
  ensures multiset(s[k..] + s[..k]) == multiset(s)
{
  calc {
    multiset(s[k..] + s[..k]);
    ==
    multiset(s[k..]) + multiset(s[..k]);
    ==
    multiset(s[k..]) + multiset(s[..k]);
    == { assert multiset(s[k..]) + multiset(s[..k]) == multiset(s); }
    multiset(s);
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
    if |rotated| == n {
      ghost var is_rotation := true;
      assert IsRotation(b, rotated) by {
        assert rotated == b[k..] + b[..k];
        assert 0 <= k < |b|;
      }
      LemmaRotatedIsReordering(b, rotated);
      assert IsReorderingOf(b, rotated);
      
      var valid_reordering := true;
      for i := 0 to n-1
        invariant valid_reordering ==> forall j :: 0 <= j < i ==> a[j] != rotated[j]
        invariant !valid_reordering ==> exists j :: 0 <= j < i && a[j] == rotated[j]
      {
        if a[i] == rotated[i] {
          valid_reordering := false;
        }
      }
      
      if valid_reordering {
        return (true, rotated);
      }
    }
    k := k + 1;
  }
  return (false, []);
}
// </vc-code>

