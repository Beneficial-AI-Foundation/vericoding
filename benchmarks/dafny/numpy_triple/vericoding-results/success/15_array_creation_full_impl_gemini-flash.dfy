// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Full<T>(n: nat, fillValue: T) returns (result: seq<T>)
  // The result has exactly n elements
  ensures |result| == n
  
  // Core property: every element equals fillValue
  ensures forall i :: 0 <= i < |result| ==> result[i] == fillValue
  
  // Uniformity property: all elements are equal to each other
  ensures forall i, j :: 0 <= i < |result| && 0 <= j < |result| ==> result[i] == result[j]
  
  // First element property (when n > 0)
  ensures n > 0 ==> (|result| > 0 && result[0] == fillValue)
  
  // Last element property (when n > 0)  
  ensures n > 0 ==> (|result| > 0 && result[|result|-1] == fillValue)
  
  // Relationship to sequence repetition (conceptual equivalence)
  ensures result == seq(n, i => fillValue)
// </vc-spec>
// <vc-code>
{
  var s: seq<T> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |s| == i
    invariant forall k :: 0 <= k < i ==> s[k] == fillValue
  {
    s := s + [fillValue];
    i := i + 1;
  }
  result := s;
}
// </vc-code>
