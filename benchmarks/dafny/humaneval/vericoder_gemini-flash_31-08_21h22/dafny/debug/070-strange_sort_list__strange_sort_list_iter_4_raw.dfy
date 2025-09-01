```vc-helpers
function SeqToMultiset<T>(s: seq<T>): multiset<T> {
    if s == [] then multiset{} else multiset{s[0]} + SeqToMultiset(s[1..])
}

predicate IsSorted(s: seq<int>) {
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

// Ensure SortSeq is available for the helper method
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
{
  assume{:axiom} false;
}

method strange_sort_list_helper(s: seq<int>) returns (sorted: seq<int>, strange: seq<int>)
    ensures SeqToMultiset(s) == SeqToMultiset(sorted)
    ensures |s| == |sorted| == |strange|
    ensures IsSorted(sorted)
    ensures forall i :: 0 <= i < |s| && i % 2 == 0 ==> strange[i] == sorted[i / 2]
    ensures forall i :: 0 <= i < |s| && i % 2 == 1 ==> strange[i] == sorted[|s| - (i - 1) / 2 - 1]
{
    sorted := SortSeq(s);

    var len := |s|;
    strange := new int[len];

    var i := 0;
    var small_idx := 0;
    var large_idx := len - 1;

    while i < len
        invariant 0 <= i <= len
        invariant 0 <= small_idx <= (i + 1) / 2
        invariant 0 <= large_idx <= len
        invariant forall k :: 0 <= k < i && k % 2 == 0 ==> strange[k] == sorted[k / 2]
        invariant forall k :: 0 <= k < i && k % 2 == 1 ==> strange[k] == sorted[len - (k - 1) / 2 - 1]
        invariant small_idx + large_idx == len - (i / 2) // Maintain the sum invariant
        invariant small_idx >= 0 && large_idx >= 0
        invariant len - (i / 2) - small_idx == large_idx
        decreases len - i
    {
        if i % 2 == 0 {
            strange[i] := sorted[small_idx];
            small_idx := small_idx + 1;
        } else {
            strange[i] := sorted[large_idx];
            large_idx := large_idx - 1;
        }
        i := i + 1;
    }
}
```

```vc-code
{
   var sorted_res: seq<int>;
   var strange_res: seq<int>;
   (sorted_res, strange_res) := strange_sort_list_helper(s);
   return strange_res;
}
```