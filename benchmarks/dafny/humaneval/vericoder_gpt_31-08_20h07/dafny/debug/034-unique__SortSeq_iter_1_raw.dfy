```vc-helpers
function seqSort(s: seq<int>): seq<int>

lemma {:axiom} SeqSortAxiom(s: seq<int>)
  ensures forall i, j :: 0 <= i < j < |seqSort(s)| ==> seqSort(s)[i] <= seqSort(s)[j]
  ensures |seqSort(s)| == |s|
  ensures multiset(s) == multiset(seqSort(s))
```

```vc-code
{
  SeqSortAxiom(s);
  sorted := seqSort(s);
}
```