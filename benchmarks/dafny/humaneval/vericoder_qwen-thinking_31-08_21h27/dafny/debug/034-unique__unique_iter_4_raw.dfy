

```vc-helpers
function uniqueSorted(s: seq<int>) returns (result: seq<int>)
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
    {:axiom}

function SortSeq(s: seq<int>) returns (sorted: seq<int>)
    ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
    ensures |sorted| == |s|
    ensures multiset(s) == multiset(sorted)
    {:axiom}
```

```vc-code
{ return uniqueSorted(SortSeq(s)); }
```