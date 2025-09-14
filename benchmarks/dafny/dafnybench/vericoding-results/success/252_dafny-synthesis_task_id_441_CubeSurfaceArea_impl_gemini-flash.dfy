

// <vc-helpers>
lemma MulIsCommutative(a: int, b: int)
  ensures a * b == b * a
{
}

lemma MulIsAssociative(a: int, b: int, c: int)
  ensures (a * b) * c == a * (b * c)
{
}
// </vc-helpers>

// <vc-spec>
method CubeSurfaceArea(size: int) returns (area: int)
    requires size > 0
    ensures area == 6 * size * size
// </vc-spec>
// <vc-code>
{
  var s_sq := size * size;
  area := 6 * s_sq;

  // Proof that area == 6 * size * size
  // This is direct from the assignment of s_sq and area.
  // No explicit lemmas are strictly necessary for simple arithmetic operations
  // that Dafny can directly reason about, but they are shown here for completeness
  // if more complex reasoning were required.
  assert s_sq == size * size;
  assert area == 6 * s_sq;
  assert area == 6 * (size * size);
}
// </vc-code>

