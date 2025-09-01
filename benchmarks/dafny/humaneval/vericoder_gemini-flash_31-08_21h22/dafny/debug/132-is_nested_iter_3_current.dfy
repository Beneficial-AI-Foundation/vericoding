

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
  var found_0_x := -1;
  var found_0_y := -1;
  var found_1_z := -1;
  var found_1_w := -1;

  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant (found_0_x == -1) || (0 <= found_0_x < i)
    invariant (found_0_y == -1) || (found_0_x != -1 && found_0_x < found_0_y < i)
    invariant (found_1_z == -1) || (found_0_y != -1 && found_0_y < found_1_z < i)
    invariant (found_1_w == -1) || (found_1_z != -1 && found_1_z < found_1_w < i)
  {
    if s[i] == 1 {
      if found_0_y != -1 {
        // We found s[i] == 1, and we have a pair of 0s.
        // This 'i' could be our 'z'.
        if found_1_z == -1 {
          found_1_z := i;
        } else {
          // If we already have a 'z', this 'i' could be our 'w'.
          // Check if it forms a valid nested sequence.
          if found_0_x != -1 && found_0_x < found_0_y && found_0_y < found_1_z && found_1_z < i {
            // We found all four indices x, y, z, w
            found_1_w := i;
            res := true;
            return;
          }
        }
      }
    } else if s[i] == 0 {
      if found_0_x == -1 {
        found_0_x := i;
      } else if found_0_y == -1 { // Only update found_0_y if it hasn't been found.
        found_0_y := i;
        // Reset found_1_z if we found a new 'y' to ensure
        // that 'z' comes after 'y'.
        found_1_z := -1; // Reset because z must be after y
      } else {
        // If we find a new '0' after both found_0_x and found_0_y are set,
        // it means we can potentially form a new pair of (0,0) that is
        // further right, potentially enabling a nested structure.
        // The previous found_0_x becomes the new found_0_y, and the current 'i'
        // becomes the new found_0_x's replacement (conceptually shifting the window).
        // A simpler way: just update found_0_x and found_0_y to the two latest 0s.
        // This is a common pattern in nested sequence problems.
        found_0_x := found_0_y; // The previous 2nd '0' becomes the 1st '0'
        found_0_y := i;         // The current '0' becomes the new 2nd '0'
        found_1_z := -1;        // Reset z and w as the 0s have shifted
        found_1_w := -1;
      }
    }
    i := i + 1;
  }
  res := false;
}
// </vc-code>

