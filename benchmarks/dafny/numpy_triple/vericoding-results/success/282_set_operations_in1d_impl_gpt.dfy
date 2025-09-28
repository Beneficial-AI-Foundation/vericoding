// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): membership predicate for sequence */
function ExistsIn<T(==)>(x: T, s: seq<T>): bool {
  exists j :: 0 <= j < |s| && x == s[j]
}
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
  /* code modified by LLM (iteration 2): replaced seq comprehension with loops to build result and prove spec */
  var r: seq<bool> := [];
  var i := 0;
  while i < |ar1|
    invariant 0 <= i <= |ar1|
    invariant |r| == i
    invariant forall k :: 0 <= k < i ==> (r[k] <==> exists j :: 0 <= j < |ar2| && ar1[k] == ar2[j])
  {
    var found := false;
    var j := 0;
    while j < |ar2|
      invariant 0 <= j <= |ar2|
      invariant found ==> exists jj :: 0 <= jj < j && ar1[i] == ar2[jj]
      invariant !found ==> (forall jj :: 0 <= jj < j ==> ar1[i] != ar2[jj])
    {
      if ar1[i] == ar2[j] {
        found := true;
      }
      j := j + 1;
    }
    assert j == |ar2|;
    assert found ==> exists jj :: 0 <= jj < |ar2| && ar1[i] == ar2[jj];
    assert !found ==> !(exists jj :: 0 <= jj < |ar2| && ar1[i] == ar2[jj]);
    r := r + [found];
    i := i + 1;
  }
  result := r;
}
// </vc-code>
