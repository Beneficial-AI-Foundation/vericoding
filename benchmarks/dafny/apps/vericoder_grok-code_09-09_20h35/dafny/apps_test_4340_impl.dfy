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
// No changes needed
// </vc-helpers>

// <vc-spec>
method solve(a: seq<int>) returns (result: seq<int>)
    ensures ValidTransformation(a, result)
// </vc-spec>
// <vc-code>
{
  var res := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |res| == i
    invariant forall j :: 0 <= j < i ==> res[j] == TransformElement(a[j])
  {
    res := res + [TransformElement(a[i])];
    i := i + 1;
  }
  result := res;
}
// </vc-code>

