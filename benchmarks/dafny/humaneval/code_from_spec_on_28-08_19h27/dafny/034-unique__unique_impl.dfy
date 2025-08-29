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

// <vc-helpers>
lemma ElementInSequence(s: seq<int>, x: int, i: int)
  requires 0 <= i < |s|
  requires s[i] == x
  ensures x in s
{
}

lemma UniqueElementsStrictlyIncreasing(s: seq<int>)
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
  ensures forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j]
{
}

lemma SortedSequenceProperty(s: seq<int>, i: int, j: int)
  requires forall k, l :: 0 <= k < l < |s| ==> s[k] <= s[l]
  requires 0 <= i < j < |s|
  ensures s[i] <= s[j]
{
}

lemma MaintainStrictOrdering(result: seq<int>, s: seq<int>, i: int)
  requires forall k, l :: 0 <= k < l < |s| ==> s[k] <= s[l]
  requires 0 <= i < |s|
  requires forall k, l :: 0 <= k < l < |result| ==> result[k] < result[l]
  requires |result| > 0 ==> result[|result|-1] < s[i]
  ensures forall k, l :: 0 <= k < l < |result + [s[i]]| ==> (result + [s[i]])[k] < (result + [s[i]])[l]
{
}

lemma SortedPropertyPersists(s: seq<int>, i: int)
  requires forall k, l :: 0 <= k < l < |s| ==> s[k] <= s[l]
  requires 0 <= i < |s|
  ensures forall k, l :: i <= k < l < |s| ==> s[k] <= s[l]
{
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method unique(s: seq<int>) returns (result: seq<int>)
Process input. Ensures: the condition holds for all values; the condition holds for all values; the condition holds for all values.
*/
// </vc-description>

// <vc-spec>
method unique(s: seq<int>) returns (result: seq<int>)
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
  ensures forall x :: x in result ==> x in s
  ensures forall x :: x in s ==> x in result
// </vc-spec>
// <vc-code>
{
  result := [];
  var i := 0;
  
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall k, l :: 0 <= k < l < |result| ==> result[k] < result[l]
    invariant forall x :: x in result ==> x in s
    invariant forall x :: x in s[..i] ==> x in result
    invariant |result| > 0 && i < |s| ==> result[|result|-1] <= s[i]
  {
    if |result| == 0 || result[|result|-1] != s[i] {
      result := result + [s[i]];
    }
    i := i + 1;
  }
}
// </vc-code>

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
{
  assume{:axiom} false;
}