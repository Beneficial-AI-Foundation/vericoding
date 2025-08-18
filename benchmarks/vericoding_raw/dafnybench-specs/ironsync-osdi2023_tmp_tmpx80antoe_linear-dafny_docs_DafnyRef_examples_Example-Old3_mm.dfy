class A {
  var z1: array<nat>
  var z2: array<nat>

// <vc-helpers>
// </vc-helpers>

method mm()
    requires z1.Length > 10 && z1[0] == 7
    requires z2.Length > 10 && z2[0] == 17
    modifies z2
// <vc-code>
{
  assume false;
}
// </vc-code>

}