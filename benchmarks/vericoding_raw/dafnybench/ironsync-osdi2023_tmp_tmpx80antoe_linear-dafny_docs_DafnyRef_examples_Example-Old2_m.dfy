class A {
  var value: int
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
// <vc-code>
{
  assume false;
}
// </vc-code>

}