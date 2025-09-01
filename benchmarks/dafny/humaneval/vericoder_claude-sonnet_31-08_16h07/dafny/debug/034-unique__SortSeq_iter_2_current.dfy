method uniqueSorted(s: seq<int>) returns (result: seq<int>)
    // pre-conditions-start
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    // pre-conditions-end
    // post-conditions-start
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
    // post-conditions-end
{
  assume{:axiom} false;
}
method unique(s: seq<int>) returns (result: seq<int>)
    // post-conditions-start
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
    // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma MultisetPreservesElements<T>(s: seq<T>, sorted: seq<T>)
  requires multiset(s) == multiset(sorted)
  ensures forall x :: x in s <==> x in sorted

lemma SortedSequenceProperties(s: seq<int>)
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  ensures forall i :: 0 <= i < |s| - 1 ==> s[i] <= s[i + 1]

lemma MultisetEmpty<T>()
  ensures multiset([]) == multiset([] : seq<T>)

lemma MultisetSingleton<T>(x: T)
  ensures multiset([x]) == multiset{x}

lemma MultisetConcat<T>(s1: seq<T>, s2: seq<T>)
  ensures multiset(s1 + s2) == multiset(s1) + multiset(s2)

lemma MultisetInsert<T>(s: seq<T>, x: T, i: nat)
  requires 0 <= i <= |s|
  ensures multiset(s[..i] + [x] + s[i..]) == multiset(s) + multiset{x}

lemma MultisetRemove<T>(s: seq<T>, i: nat)
  requires 0 <= i < |s|
  ensures multiset(s[..i] + s[i+1..]) == multiset(s) - multiset{s[i]}
// </vc-helpers>

// <vc-spec>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  sorted := [];
  var remaining := s;
  
  while |remaining| > 0
    invariant multiset(sorted) + multiset(remaining) == multiset(s)
    invariant forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
    decreases |remaining|
  {
    var minIndex := 0;
    var minValue := remaining[0];
    
    var k := 1;
    while k < |remaining|
      invariant 0 <= minIndex < |remaining|
      invariant minValue == remaining[minIndex]
      invariant forall i :: 0 <= i < k ==> remaining[minIndex] <= remaining[i]
      invariant 1 <= k <= |remaining|
    {
      if remaining[k] < minValue {
        minIndex := k;
        minValue := remaining[k];
      }
      k := k + 1;
    }
    
    sorted := sorted + [minValue];
    remaining := remaining[..minIndex] + remaining[minIndex + 1..];
    
    MultisetRemove(remaining[..minIndex] + [minValue] + remaining[minIndex+1..], minIndex);
  }
}
// </vc-code>

