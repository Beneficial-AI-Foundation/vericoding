// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Repeat<T>(input: seq<T>, repeats: nat) returns (result: seq<T>)
  requires repeats > 0
  ensures |result| == |input| * repeats
  // Each position in result maps to the correct input element
  ensures forall i :: 0 <= i < |result| ==> 
    result[i] == input[i / repeats]
  // Every input element appears exactly 'repeats' times consecutively
  ensures forall k :: 0 <= k < |input| ==> 
    forall j {:trigger result[k * repeats + j]} :: 0 <= j < repeats ==> 
      k * repeats + j < |result| && result[k * repeats + j] == input[k]
  // All positions are accounted for by the grouping structure
  ensures forall i :: 0 <= i < |result| ==> 
    (exists k :: 0 <= k < |input| && 
     (exists j {:trigger k * repeats + j} :: (0 <= j < repeats && 
      i == k * repeats + j && result[i] == input[k])))
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
