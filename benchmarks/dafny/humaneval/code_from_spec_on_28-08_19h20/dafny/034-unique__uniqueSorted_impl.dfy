// <vc-helpers>
method removeElement(s: seq<int>, x: int) returns (result: seq<int>)
    ensures forall y :: y in result ==> y in s && y != x
    ensures forall y :: y in s && y != x ==> y in result
    ensures |result| <= |s|
{
    result := [];
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall y :: y in result ==> y in s && y != x
        invariant forall j :: 0 <= j < i && s[j] != x ==> s[j] in result
    {
        if s[i] != x {
            result := result + [s[i]];
        }
        i := i + 1;
    }
}

method removeDuplicates(s: seq<int>) returns (result: seq<int>)
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
{
    result := s;
    var processed := [];
    var i := 0;
    
    while i < |result|
        invariant 0 <= i <= |result|
        invariant forall x :: x in result ==> x in s
        invariant forall x :: x in s ==> x in result
        invariant forall j, k :: 0 <= j < k < i ==> result[j] != result[k]
        invariant |processed| == i
        invariant forall j :: 0 <= j < i ==> processed[j] == result[j]
    {
        var j := i + 1;
        while j < |result|
            invariant i < j <= |result|
            invariant forall x :: x in result ==> x in s
            invariant forall x :: x in s ==> x in result
            invariant forall k, l :: 0 <= k < l < i ==> result[k] != result[l]
            invariant forall k :: i < k < j ==> result[k] != result[i]
        {
            if result[j] == result[i] {
                result := result[..j] + result[j+1..];
            } else {
                j := j + 1;
            }
        }
        processed := processed + [result[i]];
        i := i + 1;
    }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method uniqueSorted(s: seq<int>) returns (result: seq<int>)
Sort elements. Requires: the condition holds for all values. Ensures: the condition holds for all values; the condition holds for all values; the condition holds for all values.
*/
// </vc-description>

// <vc-spec>
method uniqueSorted(s: seq<int>) returns (result: seq<int>)
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
// </vc-spec>
// <vc-code>
method uniqueSorted(s: seq<int>) returns (result: seq<int>)
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
{
    var uniqueSeq := removeDuplicates(s);
    var sorted := SortSeq(uniqueSeq);
    result := sorted;
}
// </vc-code>

method unique(s: seq<int>) returns (result: seq<int>)
    // post-conditions-start
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
    // post-conditions-end
{
  assume{:axiom} false;
}
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
{
  assume{:axiom} false;
}