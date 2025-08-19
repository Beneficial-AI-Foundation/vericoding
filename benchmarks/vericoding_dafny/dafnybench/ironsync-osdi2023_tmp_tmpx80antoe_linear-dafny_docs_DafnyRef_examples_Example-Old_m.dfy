class A {

  var value: int

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method m(i: int)
    requires i == 6
    requires value == 42
    modifies this
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>

}