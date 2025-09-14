

// <vc-helpers>
/**
 * A helper function to check if an element exists in a sequence.
 * This is useful for `in` checks on sequences.
 */
function SeqContains(s: seq<int>, x: int): bool {
  exists i :: 0 <= i < |s| && s[i] == x
}
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
    invariant !(exists j :: 0 <= j < i && SeqContains(seq2, seq1[j]))
    decreases |seq1| - i
  {
    if SeqContains(seq2, seq1[i]) {
      return true;
    }
    i := i + 1;
  }
  return false;
}
// </vc-code>

