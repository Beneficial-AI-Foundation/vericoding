

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method derivative(xs: seq<int>) returns (result: seq<int>)
  // pre-conditions-start
  requires |xs| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures |result| == |xs| - 1
  ensures forall i :: 0 <= i < |result| ==> result[i] == xs[i+1] * (i+1)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
var res: seq<int> := [];
var i := 0;
while i < |xs| - 1
  invariant 0 <= i <= |xs| - 1
  invariant |res| == i
  invariant forall j :: 0 <= j < i ==> res[j] == xs[j + 1] * (j + 1)
{
  res := res + [xs[i + 1] * (i + 1)];
  i := i + 1;
}
result := res;
}
// </vc-code>

