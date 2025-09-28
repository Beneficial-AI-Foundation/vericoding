// <vc-preamble>
// Method to create a sequence of zeros of given length
// </vc-preamble>

// <vc-helpers>

function zerosInit<T>(n: nat, zero: T): seq<T>
  ensures |zerosInit(n, zero)| == n
  ensures forall i :: 0 <= i < n ==> zerosInit(n, zero)[i] == zero
{
  if n == 0 then [] else [zero] + zerosInit(n - 1, zero)
}

// </vc-helpers>

// <vc-spec>
method zeros<T>(n: nat, zero: T) returns (result: seq<T>)
    ensures |result| == n
    // All elements are zero
    ensures forall i :: 0 <= i < |result| ==> result[i] == zero
// </vc-spec>
// <vc-code>
{
  result := zerosInit(n, zero);
}
// </vc-code>
