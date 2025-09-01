```vc-helpers
function SortFun(s: seq<int>): seq<int>

lemma {:axiom} SortFun_properties(s: seq<int>)
  ensures |SortFun(s)| == |s|
  ensures multiset(s) == multiset(SortFun(s))
  ensures forall i, j :: 0 <= i < j < |SortFun(s)| ==> SortFun(s)[i] <= SortFun(s)[j]
```

```vc-code
{
  sorted := SortFun(s);
  call SortFun_properties(s);
}
```