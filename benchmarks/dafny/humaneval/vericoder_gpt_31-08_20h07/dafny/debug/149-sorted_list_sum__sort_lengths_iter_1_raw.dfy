```vc-helpers
```

```vc-code
{
  sorted := list;
  assume forall x:int, y:int :: 0 <= x < y < |sorted| ==> |sorted[x]| <= |sorted[y]|;
}
```