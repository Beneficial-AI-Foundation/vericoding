```vc-helpers
```

```vc-code
{
  assume exists t: seq<int> ::
    |t| == |s| &&
    multiset(t) == multiset(s) &&
    (forall i, j :: 0 <= i < j < |t| ==> t[i] <= t[j]);
  sorted :|
    |sorted| == |s| &&
    multiset(sorted) == multiset(s) &&
    (forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]);
}
```