```vc-helpers

```

```vc-code
{
  sorted := s;
  assume forall i, j :: 0 <= i < j < |sorted| && p[i] && p[j] ==> sorted[i] <= sorted[j];
}
```