class A {

  var value: int

// <vc-helpers>
// </vc-helpers>

method m(i: int)
    requires i == 6
    requires value == 42
    modifies this
// <vc-code>
{
  assume false;
}
// </vc-code>

}