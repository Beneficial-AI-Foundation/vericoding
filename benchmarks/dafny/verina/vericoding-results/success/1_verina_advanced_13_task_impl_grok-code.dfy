// <vc-preamble>
predicate ChordIntersects(chord1: seq<nat>, chord2: seq<nat>)
    requires |chord1| == 2 && |chord2| == 2
{
    var a1 := if chord1[0] < chord1[1] then chord1[0] else chord1[1];
    var b1 := if chord1[0] > chord1[1] then chord1[0] else chord1[1];
    var a2 := if chord2[0] < chord2[1] then chord2[0] else chord2[1];
    var b2 := if chord2[0] > chord2[1] then chord2[0] else chord2[1];
    (a1 < a2 && a2 < b1 && b1 < b2) || (a2 < a1 && a1 < b2 && b2 < b1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): no changes needed */
// </vc-helpers>

// <vc-spec>
method HasChordIntersection(n: nat, chords: seq<seq<nat>>) returns (result: bool)
    requires
        n >= 2
    requires
        |chords| == n
    requires
        forall i :: 0 <= i < |chords| ==> (
            |chords[i]| == 2 &&
            chords[i][0] >= 1 && chords[i][0] <= 2 * n &&
            chords[i][1] >= 1 && chords[i][1] <= 2 * n
        )
    requires
        /* All endpoints are distinct */
        forall i, j, k, l :: 
            (0 <= i < |chords| && 0 <= j < |chords| && 
            0 <= k < 2 && 0 <= l < 2 && 
            (i != j || k != l)) ==> chords[i][k] != chords[j][l]
    ensures
        result == exists i, j :: 
            0 <= i < |chords| && 0 <= j < |chords| && i != j &&
            ChordIntersects(chords[i], chords[j])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implemented pairwise check with i < j and loop invariants to prove postcondition */
  var i := 0;
  while i < |chords|
    invariant 0 <= i <= |chords|
    invariant forall a, b :: 0 <= a < i && a < b < |chords| ==> !ChordIntersects(chords[a], chords[b])
  {
    var j := i + 1;
    while j < |chords|
      invariant i < j <= |chords|
      invariant forall b :: i < b < j ==> !ChordIntersects(chords[i], chords[b])
    {
      if ChordIntersects(chords[i], chords[j]) {
        return true;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  return false;
}
// </vc-code>
