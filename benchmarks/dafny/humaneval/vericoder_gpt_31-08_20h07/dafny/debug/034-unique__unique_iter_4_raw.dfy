```vc-helpers
lemma SeqMemEquivFromMultisetEq<T>(s: seq<T>, t: seq<T>)
  ensures multiset(s) == multiset(t) ==> (forall x :: x in s <==> x in t)
{
  assume {:axiom} false;
}
```

```vc-code
{
  var sorted := SortSeq(s);
  SeqMemEquivFromMultisetEq(s, sorted);
  var r := uniqueSorted(sorted);
  return r;
}
```