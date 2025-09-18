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
function MinEndpoint(ch: seq<nat>): nat
    requires |ch| == 2
    {
        if ch[0] < ch[1] then ch[0] else ch[1]
    }

function MaxEndpoint(ch: seq<nat>): nat
    requires |ch| == 2
    {
        if ch[0] > ch[1] then ch[0] else ch[1]
    }
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
  var m := |chords|;
  var i := 0;
  while i < m
    invariant 0 <= i <= m
    invariant forall i0, j0 :: 0 <= i0 < i && 0 <= j0 < m && i0 != j0 ==> !ChordIntersects(chords[i0], chords[j0])
    decreases m - i
  {
    var j := i + 1;
    while j < m
      invariant i + 1 <= j <= m
      invariant forall j0 :: i < j0 < j ==> !ChordIntersects(chords[i], chords[j0])
      invariant forall i0, j0 :: 0 <= i0 < i && 0 <= j0 < m && i0 != j0 ==> !ChordIntersects(chords[i0], chords[j0])
      decreases m - j
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
