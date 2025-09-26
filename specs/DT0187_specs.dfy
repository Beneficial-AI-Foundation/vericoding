// <vc-preamble>
// Helper function to count the number of True values in a boolean sequence
function CountTrue(mask: seq<bool>): nat
{
  if |mask| == 0 then 0
  else (if mask[0] then 1 else 0) + CountTrue(mask[1..])
}

// Helper function to get the position of the i-th True element in the mask
function GetTruePosition(mask: seq<bool>, i: nat, trueIndex: nat): nat
  requires i < |mask|
  requires trueIndex < CountTrue(mask[i..])
  decreases |mask| - i
{
  if mask[i] then
    if trueIndex == 0 then i
    else GetTruePosition(mask, i + 1, trueIndex - 1)
  else
    GetTruePosition(mask, i + 1, trueIndex)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Place(arr: seq<real>, mask: seq<bool>, vals: seq<real>, k: nat) returns (result: seq<real>)
  // Array and mask must have the same length
  requires |arr| == |mask|
  // Values array must be non-empty
  requires |vals| > 0
  // k represents the count of True elements in mask
  requires k == CountTrue(mask)
  // Result has same length as input array
  ensures |result| == |arr|
  // Elements where mask is False remain unchanged
  ensures forall i :: 0 <= i < |result| ==> !mask[i] ==> result[i] == arr[i]
  // Elements where mask is True are replaced with values from vals (with repetition)
  ensures forall i :: 0 <= i < |result| ==> mask[i] ==> 
    exists pos :: 0 <= pos < CountTrue(mask) &&
                  GetTruePosition(mask, 0, pos) == i &&
                  result[i] == vals[pos % |vals|]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
