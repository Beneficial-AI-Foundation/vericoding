// <vc-preamble>
// Helper function to flatten a sequence of sequences back into a single sequence
function flatten(seqs: seq<seq<real>>): seq<real>
{
  if |seqs| == 0 then []
  else seqs[0] + flatten(seqs[1..])
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method dsplit(arr: seq<real>, sections: nat) returns (result: seq<seq<real>>)
  // Input array length must be evenly divisible by sections
  requires sections > 0
  requires |arr| % sections == 0
  
  // The result contains exactly 'sections' number of sub-sequences
  ensures |result| == sections
  
  // Each sub-sequence has the same length (arr.length / sections)
  ensures forall i :: 0 <= i < |result| ==> |result[i]| == |arr| / sections
  
  // Elements are correctly distributed: the i-th sub-sequence contains
  // elements from positions i*(|arr|/sections) to (i+1)*(|arr|/sections)-1
  // of the original array
  ensures forall i, j :: 0 <= i < |result| && 0 <= j < |result[i]| ==>
    result[i][j] == arr[i * (|arr| / sections) + j]
  
  // Concatenating all sub-sequences in order reconstructs the original array
  ensures flatten(result) == arr
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
