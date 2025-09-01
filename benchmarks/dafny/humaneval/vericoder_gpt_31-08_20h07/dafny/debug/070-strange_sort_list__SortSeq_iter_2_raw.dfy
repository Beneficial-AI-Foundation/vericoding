```vc-helpers
lemma {:axiom} SortedSeqExists(s: seq<int>)
  ensures exists sorted: seq<int> ::
    |sorted| == |s| &&
    multiset(sorted) == multiset(s) &&
    (forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j])
```

```vc-code
{
  SortedSeqExists(s);
  var t: seq<int> :| |t| == |s| &&
                     multiset(t) == multiset(s) &&
                     (forall i, j :: 0 <= i < j < |t| ==> t[i] <= t[j]);
  sorted := t;
}
```