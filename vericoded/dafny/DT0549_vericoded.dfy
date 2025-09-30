// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method In1d<T(==)>(ar1: seq<T>, ar2: seq<T>) returns (result: seq<bool>)
  // The result has the same length as the first input array
  ensures |result| == |ar1|
  // Each element in the result indicates membership: result[i] is true iff ar1[i] exists in ar2
  ensures forall i :: 0 <= i < |ar1| ==> 
    (result[i] <==> exists j :: 0 <= j < |ar2| && ar1[i] == ar2[j])
// </vc-spec>
// <vc-code>
{
  result := [];
  for i := 0 to |ar1|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> (result[k] <==> exists j :: 0 <= j < |ar2| && ar1[k] == ar2[j])
  {
    var found := false;
    for j := 0 to |ar2|
      invariant found <==> exists k :: 0 <= k < j && ar1[i] == ar2[k]
    {
      if ar1[i] == ar2[j] {
        found := true;
      }
    }
    result := result + [found];
  }
}
// </vc-code>
