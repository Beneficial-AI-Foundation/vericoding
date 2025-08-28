method derivative(xs: seq<int>) returns (result: seq<int>)
  // pre-conditions-start
  requires |xs| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures |result| == |xs| - 1
  ensures forall i :: 0 <= i < |result| ==> result[i] == xs[i+1] * (i+1)
  // post-conditions-end
{
  // impl-start
  result := [];
  var i := 1;
  while i < |xs|
    // invariants-start
    invariant 1 <= i <= |xs|
    invariant |result| == i - 1
    invariant forall j :: 0 <= j < |result| ==> result[j] == xs[j+1] * (j+1)
    // invariants-end
  {
    result := result + [xs[i] * i];
    i := i + 1;
  }
  // impl-end
}
