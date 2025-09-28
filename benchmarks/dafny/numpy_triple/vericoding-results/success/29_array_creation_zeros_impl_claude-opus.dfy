// <vc-preamble>
// Method to create a sequence of zeros of given length
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method zeros<T>(n: nat, zero: T) returns (result: seq<T>)
    ensures |result| == n
    // All elements are zero
    ensures forall i :: 0 <= i < |result| ==> result[i] == zero
// </vc-spec>
// <vc-code>
{
  result := [];
  var i := 0;
  while i < n
    invariant i <= n
    invariant |result| == i
    invariant forall j :: 0 <= j < |result| ==> result[j] == zero
  {
    result := result + [zero];
    i := i + 1;
  }
}
// </vc-code>
