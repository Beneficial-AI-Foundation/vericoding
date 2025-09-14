function TransformElement(x: int): int
{
    if x % 2 == 0 then x - 1 else x
}

predicate ValidTransformation(input: seq<int>, output: seq<int>)
{
    |output| == |input| &&
    forall i :: 0 <= i < |input| ==> output[i] == TransformElement(input[i])
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(a: seq<int>) returns (result: seq<int>)
    ensures ValidTransformation(a, result)
// </vc-spec>
// <vc-code>
{
  var temp_array := new int[|a|];
  for i := 0 to |a|
    invariant forall k :: 0 <= k < i ==> temp_array[k] == TransformElement(a[k])
  {
      temp_array[i] := TransformElement(a[i]);
  }
  result := temp_array[..];
}
// </vc-code>

