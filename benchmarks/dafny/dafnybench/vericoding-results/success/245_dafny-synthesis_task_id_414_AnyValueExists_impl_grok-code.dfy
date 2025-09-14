

// <vc-helpers>
//
// </vc-helpers>

// <vc-spec>
method AnyValueExists(seq1: seq<int>, seq2: seq<int>) returns (result: bool)
    ensures result <==> (exists i :: 0 <= i < |seq1| && seq1[i] in seq2)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < |seq1|
    invariant 0 <= i <= |seq1|
    invariant forall k :: 0 <= k < i ==> !(seq1[k] in seq2)
  {
    if seq1[i] in seq2 {
      return true;
    }
    i := i + 1;
  }
  return false;
}
// </vc-code>

