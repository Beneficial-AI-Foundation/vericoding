```vc-helpers
lemma {:axiom} Existence(s: seq<int>, p: seq<bool>)
  requires |s| == |p|
  ensures exists sorted: seq<int> ::
      |sorted| == |s| &&
      (forall i, j :: 0 <= i < j < |sorted| && p[i] && p[j] ==> sorted[i] <= sorted[j]) &&
      multiset(s) == multiset(sorted) &&
      (forall i :: 0 <= i < |s| && !p[i] ==> sorted[i] == s[i])
```

```vc-code
{
  Existence(s, p);
  sorted :| |sorted| == |s|
        && (forall i, j :: 0 <= i < j < |sorted| && p[i] && p[j] ==> sorted[i] <= sorted[j])
        && multiset(s) == multiset(sorted)
        && (forall i :: 0 <= i < |s| && !p[i] ==> sorted[i] == s[i]);
}
```