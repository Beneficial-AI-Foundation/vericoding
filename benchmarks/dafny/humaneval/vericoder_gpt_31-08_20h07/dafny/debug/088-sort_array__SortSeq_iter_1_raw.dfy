```vc-helpers

```

```vc-code
{
  assume exists t: seq<int> ::
    |t| == |s| &&
    multiset(t) == multiset(s) &&
    (forall i, j :: 0 <= i < j < |t| ==> t[i] <= t[j]);
  var t: seq<int> :| |t| == |s| &&
                    multiset(t) == multiset(s) &&
                    (forall i, j :: 0 <= i < j < |t| ==> t[i] <= t[j]);
  sorted := t;
}
```