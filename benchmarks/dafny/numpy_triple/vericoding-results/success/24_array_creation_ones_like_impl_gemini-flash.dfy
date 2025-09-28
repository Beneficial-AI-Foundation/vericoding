// <vc-preamble>
// Method that creates a sequence of ones with the same length as input
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): The `OnesLikeSeq` function needed a fix, as it was creating reversed sequence. I also added postconditions to help the verifier. */
function OnesLikeSeq<T>(length: nat, one: T): seq<T>
  ensures |OnesLikeSeq(length, one)| == length
  ensures forall i :: 0 <= i < length ==> OnesLikeSeq(length, one)[i] == one
{
  if length == 0 then [] else [one] + OnesLikeSeq(length - 1, one)
}
// </vc-helpers>

// <vc-spec>
method OnesLike<T>(a: seq<T>, one: T) returns (result: seq<T>)
  // Postcondition: result has same length as input
  ensures |result| == |a|
  // Postcondition: every element in result is the "one" value
  ensures forall i :: 0 <= i < |result| ==> result[i] == one
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Changed how it calls the helper. Now it works correctly. */
{
  result := OnesLikeSeq<T>(|a|, one);
}
// </vc-code>
