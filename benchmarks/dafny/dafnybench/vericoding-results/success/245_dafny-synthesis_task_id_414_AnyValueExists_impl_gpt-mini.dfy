

// <vc-helpers>
// No helper code needed.
// </vc-helpers>

// <vc-spec>
method AnyValueExists(seq1: seq<int>, seq2: seq<int>) returns (result: bool)
    ensures result <==> (exists i :: 0 <= i < |seq1| && seq1[i] in seq2)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var found := false;
  while i < |seq1|
    invariant 0 <= i <= |seq1|
    invariant found <==> exists k :: 0 <= k < i && seq1[k] in seq2
  {
    if seq1[i] in seq2 {
      found := true;
    }
    i := i + 1;
  }
  result := found;
}
// </vc-code>

