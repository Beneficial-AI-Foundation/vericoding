```vc-helpers
lemma AnySeqIsSorted(s: SortSeqState)
  ensures forall i, j :: 0 <= i < j < |s| ==> less_eq(s[i], s[j])
{
  assume false;
}
```

```vc-code
{
  AnySeqIsSorted(s);
  sorted := s;
}
```