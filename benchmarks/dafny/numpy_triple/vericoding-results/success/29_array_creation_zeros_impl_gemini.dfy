// <vc-preamble>
// Method to create a sequence of zeros of given length
// </vc-preamble>

// <vc-helpers>
function Zeros<T>(n: nat, zero: T): seq<T>
  ensures |Zeros(n, zero)| == n
  ensures forall k :: 0 <= k < n ==> Zeros(n, zero)[k] == zero
{
  if n == 0 then []
  else Zeros(n - 1, zero) + [zero]
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
  result := Zeros(n, zero);
}
// </vc-code>
