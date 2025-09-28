// <vc-preamble>
// Helper function to count occurrences of a value in a sequence
function CountOccurrences(s: seq<nat>, value: nat): nat
{
    |set i | 0 <= i < |s| && s[i] == value|
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method BinCount(x: seq<nat>, max_val: nat) returns (result: seq<nat>)
  // Precondition: All values in x are non-negative and ≤ max_val
  requires forall i :: 0 <= i < |x| ==> x[i] <= max_val
  // Postcondition: result has length max_val + 1
  ensures |result| == max_val + 1
  // Postcondition: result[i] = count of occurrences of value i in x
  ensures forall val :: 0 <= val < |result| ==> result[val] == CountOccurrences(x, val)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): fix type constraint by ensuring i is nat */
  result := seq(max_val + 1, (i: nat) => CountOccurrences(x, i));
}
// </vc-code>
