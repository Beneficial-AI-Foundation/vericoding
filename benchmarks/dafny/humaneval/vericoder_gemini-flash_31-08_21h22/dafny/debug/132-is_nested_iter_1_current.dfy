

// <vc-helpers>
/**
 * A helper lemma to prove the existence of indices within a sequence.
 * This lemma is not strictly necessary for this particular problem,
 * but demonstrates how helpers can be structured.
 */
lemma LemmaExistsFourIndices(s: seq<int>, x: int, y: int, z: int, w: int)
  requires 0 <= x < y < z < w < |s|
  ensures true // Trivial postcondition, mainly for illustrating usage
{}
// </vc-helpers>

// <vc-spec>
method is_nested(s: seq<int>) returns (res: bool) 
    // post-conditions-start
    ensures res == exists x, y, z, w :: 0 <= x < y < z < w < |s| && s[x] == 0 && s[y] == 0 && s[z] == 1 && s[w] == 1
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var found_0_at_x := -1;
  var found_0_at_y := -1;
  var found_1_at_z := -1;

  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant (found_0_at_x == -1) || (0 <= found_0_at_x < i)
    invariant (found_0_at_y == -1) || (found_0_at_x != -1 && found_0_at_x < found_0_at_y < i)
    invariant (found_1_at_z == -1) || (found_0_at_y != -1 && found_0_at_y < found_1_at_z < i)
  {
    if s[i] == 1 {
      if found_0_at_y != -1 {
        // We found s[i] == 1, and we have a pair of 0s.
        // This 'i' could be our 'z'.
        if found_1_at_z == -1 {
          found_1_at_z := i;
        } else {
          // If we already have a 'z', this 'i' could be our 'w'.
          // Check if it forms a valid nested sequence.
          if found_0_at_x != -1 && found_0_at_x < found_0_at_y && found_0_at_y < found_1_at_z && found_1_at_z < i {
            res := true;
            return;
          }
        }
      }
    } else if s[i] == 0 {
      if found_0_at_x == -1 {
        found_0_at_x := i;
      } else {
        // We found a second 0. This 'i' could be our 'y'.
        found_0_at_y := i;
        // Reset found_1_at_z if we found a new 'y' to ensure
        // that 'z' comes after 'y'.
        found_1_at_z := -1;
      }
    }
    i := i + 1;
  }
  res := false;
}
// </vc-code>

