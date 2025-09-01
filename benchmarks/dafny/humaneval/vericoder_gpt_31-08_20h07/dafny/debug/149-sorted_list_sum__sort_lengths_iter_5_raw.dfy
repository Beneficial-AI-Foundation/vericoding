```vc-helpers
predicate SortedByLen(s: seq<string>)
{
  forall x:int, y:int :: 0 <= x < y < |s| ==> |s[x]| <= |s[y]|
}

predicate EvenAll(s: seq<string>)
{
  forall i:int :: 0 <= i < |s| ==> |s[i]| % 2 == 0
}

lemma SortedInsert(acc: seq<string>, x: string, i:int)
  requires SortedByLen(acc)
  requires 0 <= i <= |acc|
  requires forall k:int :: 0 <= k < i ==> |acc[k]| < |x|
  requires i == |acc| || |x| <= |acc[i]|
  ensures SortedByLen(acc[..i] + [x] + acc[i..])
{
  var res := acc[..i] + [x] + acc[i..];
  assert forall p:int, q:int
           :: 0 <= p < q < |res|
           ==> |res[p]| <= |res[q]|
    by {
      assume 0 <= p < q < |res|;
      if q < i {
        assert res[p] == acc[p];
        assert res[q] == acc[q];
        assert |acc[p]| <= |acc[q]|;
      } else if p < i && q == i {
        assert res[p] == acc[p];
        assert res[q] == x;
        assert |acc[p]| < |x|;
      } else if p < i && q > i {
        assert res[p] == acc[p];
        assert res[q] == acc[q - 1];
        assert q - 1 < |acc|;
        assert p < q - 1;
        assert |acc[p]| <= |acc[q - 1]|;
      } else if p == i && q > i {
        assert res[p] == x;
        assert res[q] == acc[q - 1];
        if i < |acc| {
          assert |x| <= |acc[i]|;
          assert i < q - 1 || (q - 1) == i;
          if i < q - 1 {
            assert |acc[i]| <= |acc[q - 1]|;
          }
          assert |x| <= |acc[q - 1]|;
        } else {
          // i == |acc|, but then q > i is impossible since q < |res| == |acc| + 1
          // thus no action needed
        }
      } else if p > i && q > i {
        assert res[p] == acc[p - 1];
        assert res[q] == acc[q - 1];
        assert p - 1 < q - 1 < |acc|;
        assert |acc[p - 1]| <= |acc[q - 1]|;
      } else {
        // The remaining possibilities are covered by the above cases
      }
    }
}

lemma EvenInsertEven(acc: seq<string>, x: string, i:int)
  requires EvenAll(acc)
  requires 0 <= i <= |acc|
  requires |x| % 2 == 0
  ensures EvenAll(acc[..i] + [x] + acc[i..])
{
  var res := acc[..i] + [x] + acc[i..];
  assert forall t:int :: 0 <= t < |res| ==> |res[t]| % 2 == 0
    by {
      assume 0 <= t < |res|;
      if t < i {
        assert res[t] == acc[t];
        assert |acc[t]| % 2 == 0;
      } else if t == i {
        assert res[t] == x;
        assert |x| % 2 == 0;
      } else {
        assert t > i;
        assert res[t] == acc[t - 1];
        assert |acc[t - 1]| % 2 == 0;
      }
    }
}
```

```vc-code
{
  var acc: seq<string> := [];
  var j := 0;
  while j < |list|
    invariant 0 <= j <= |list|
    invariant |acc| == j
    invariant multiset(acc) == multiset(list[..j])
    invariant SortedByLen(acc)
    invariant EvenAll(acc)
    decreases |list| - j
  {
    var x := list[j];
    var i := 0;
    while i < |acc| && |acc[i]| < |x|
      invariant 0 <= i <= |acc|
      invariant forall k:int :: 0 <= k < i ==> |acc[k]| < |x|
      decreases |acc| - i
    {
      i := i + 1;
    }
    assert i == |acc| || |x| <= |acc[i]|;
    // preserve sortedness
    SortedInsert(acc, x, i);
    // preserve evenness
    assert 0 <= j < |list|;
    assert |x| % 2 == 0;
    EvenInsertEven(acc, x, i);
    // update accumulator
    acc := acc[..i] + [x] + acc[i..];
    assert |acc| == j + 1;
    // update multiset invariant
    assert multiset(acc) == multiset(acc[..i]) + multiset([x]) + multiset(acc[i..]);
    assert multiset(acc[..i] + acc[i..]) == multiset(acc[..i]) + multiset(acc[i..]);
    assert multiset(acc) == multiset((acc[..i] + acc[i..])) + multiset([x]);
    // But acc[..i] + acc[i..] equals the previous acc without x, which had length j
    // We need to relate to list[..j+1]
    // Using old relation: multiset(old acc) == multiset(list[..j])
    // Conclude:
    // multiset(acc) == multiset(list[..j]) + multiset([x])
    assert multiset(acc) == multiset(list[..j]) + multiset([x]);
    assert multiset(list[..j] + [x]) == multiset(list[..j]) + multiset([x]);
    assert multiset(acc) == multiset(list[..j] + [x]);
    assert list[..j] + [x] == list[..j + 1];
    j := j + 1;
  }
  sorted := acc;
}
```