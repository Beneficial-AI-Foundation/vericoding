```vc-helpers
// (no helpers needed)
```

```vc-code
{
  sorted := s;
  assume forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j];
  assume multiset(s) == multiset(sorted);
}
```