class A {
  var value: int
// <vc-spec>
  constructor ()
     ensures value == 10
  {
     value := 10;
  }
}

class B {
   var a: A
   constructor () { a := new A(); }

// <vc-helpers>
// </vc-helpers>

method m()
     requires a.value == 11
     modifies this, this.a
// </vc-spec>
// <vc-code>
{
}
// </vc-code>

}