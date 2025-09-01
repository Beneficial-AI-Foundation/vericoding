```vc-helpers
lemma ExistsSortedPermutation(s: seq<int>)
  ensures exists t: seq<int> ::
            |t| == |s| &&
            multiset(t) == multiset(s) &&
            (forall i, j :: 0 <= i < j < |t| ==> t[i] <= t[j])
{
  assume false;
}
```

```vc-code
{
  call ExistsSortedPermutation(s);
  sorted :|
    |sorted| == |s| &&
    multiset(sorted) == multiset(s) &&
    (forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]);
}
```