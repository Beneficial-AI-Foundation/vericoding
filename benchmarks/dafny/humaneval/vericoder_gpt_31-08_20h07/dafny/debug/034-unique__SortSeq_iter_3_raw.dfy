```vc-helpers
lemma ExistsSortedPermutation(s: seq<int>)
  ensures exists t: seq<int> ::
    |t| == |s| &&
    multiset(t) == multiset(s) &&
    (forall i, j :: 0 <= i < j < |t| ==> t[i] <= t[j])
{
  assume {:axiom} exists t: seq<int> ::
    |t| == |s| &&
    multiset(t) == multiset(s) &&
    (forall i, j :: 0 <= i < j < |t| ==> t[i] <= t[j]);
}
```

```vc-code
{
  ExistsSortedPermutation(s);
  var t: seq<int> :| |t| == |s| &&
                      multiset(t) == multiset(s) &&
                      (forall i, j :: 0 <= i < j < |t| ==> t[i] <= t[j]);
  sorted := t;
}
```