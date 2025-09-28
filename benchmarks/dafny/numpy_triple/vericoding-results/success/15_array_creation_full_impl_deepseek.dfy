// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function seqFillProperty<T(==)>(s: seq<T>, n: nat, fillValue: T): bool
  requires |s| == n
  ensures seqFillProperty(s, n, fillValue) <==> forall i :: 0 <= i < n ==> s[i] == fillValue
{
  if n == 0 then
    true
  else
    s[0] == fillValue && seqFillProperty(s[1..], n - 1, fillValue)
}
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
  /* code modified by LLM (iteration 2): Fixed compilation error by adding equality constraint */
  if n == 0 {
    result := [];
  } else {
    var tail : seq<T> := Full(n - 1, fillValue);
    result := [fillValue] + tail;
    assert seqFillProperty(result, n, fillValue);
  }
}
// </vc-code>
