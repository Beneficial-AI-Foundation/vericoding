```vc-helpers
function evenMask(n: nat): seq<bool>
  decreases n
  ensures |evenMask(n)| == n
  ensures forall i :: 0 <= i < n ==> evenMask(n)[i] == (i % 2 == 0)
{
  if n == 0 then []
  else evenMask(n - 1) + [((n - 1) % 2 == 0)]
}
```

```vc-code
{
  var p := evenMask(|a|);
  sorted := SortSeqPred(a, p);

  assert |p| == |a|;
  assert |sorted| == |a|;

  assert forall i:int :: 0 <= i < |a| && i % 2 == 1 ==> sorted[i] == a[i]
  {
    assume 0 <= i < |a| && i % 2 == 1;
    assert |p| == |a|;
    assert 0 <= i < |p|;
    assert p[i] == (i % 2 == 0);
    assert !p[i];
    assert |sorted| == |a|;
    assert 0 <= i < |sorted|;
    assert sorted[i] == a[i];
  }

  assert forall i:int, j:int ::
      0 <= i < j && 2 * i < |sorted| && 2 * j < |sorted| ==>
        sorted[2 * i] <= sorted[2 * j]
  {
    assume 0 <= i < j && 2 * i < |sorted| && 2 * j < |sorted|;
    assert 0 <= 2 * i;
    assert 2 * i < 2 * j;
    assert 2 * j < |sorted|;
    assert |sorted| == |a|;
    assert |p| == |a|;
    assert 2 * i < |p| && 2 * j < |p|;
    assert p[2 * i] == ((2 * i) % 2 == 0);
    assert p[2 * j] == ((2 * j) % 2 == 0);
    assert (2 * i) % 2 == 0 && (2 * j) % 