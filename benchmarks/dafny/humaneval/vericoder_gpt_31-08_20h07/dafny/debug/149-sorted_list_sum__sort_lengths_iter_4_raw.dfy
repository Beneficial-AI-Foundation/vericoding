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
  assert |res| == |acc| + 1;
  assert forall p:int, q:int
           :: 0 <= p < q < |res|
           ==> |res[p]| <= |res[q]|
    by {
      assume 0 <= p < q < |res|;
      if q < i {
        assert res[p] == acc[p];
        assert res[q] == acc[q];
        assert 0 <= p < q < |acc|;
        assert |acc[p]| <= |acc[q]|;
      } else if p < i && q == i {
        assert res[p] == acc[p];
        assert res[q] == x;
        assert 0 <= p < i;
        assert |acc[p]| < |x|;
        assert |acc[p]| <= |x|;
      } else if p < i && q > i {
        assert res[p] == acc[p];
        assert res[q] == acc[q - 1];
        assert q - 1 < |acc|;
        assert i <= q - 1;
        assert p < q - 1;
        assert |acc[p]| <= |acc[q - 1]|;
      } else if p == i && q > i {
        assert res[p] == x;
        assert res[q] == acc[q - 1];
        assert q < |acc| + 1;
        assert i < |acc|; // since q > i and q < |acc| + 1
        assert i <= q - 1;
        assert |x| <= |acc[i]|;
        if i == q - 1 {
          assert |x| <= |acc[q - 1]|;
        } else {
          assert i < q - 1 < |acc|;
          assert |acc[i]| <= |acc[q - 1]|;
          assert |x| <= |acc[q - 1]|;
        }
      } else {
        assert p > i && q > i;
        assert res[p] == acc[p - 1];
        assert res[q] == acc[q - 1];
        assert 0 <= p - 1 < q - 1 < |acc|;
        assert |acc[p - 1]| <= |acc[q - 1]|;
      }
    }
}

lemma EvenInsert(acc: seq<string>, x: string, i: int)
  requires EvenAll(acc)
  requires |x| % 2 == 0
  requires 0 <= i <= |acc|
  ensures EvenAll(acc[..i] + [x] + acc[i..])
{
  var res := acc[..i] + [x] + acc[i..];
  assert forall j:int :: 0