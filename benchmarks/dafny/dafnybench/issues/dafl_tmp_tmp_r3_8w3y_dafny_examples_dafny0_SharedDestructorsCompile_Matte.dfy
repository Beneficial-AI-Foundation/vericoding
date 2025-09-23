// <vc-preamble>
// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

datatype Dt =
  | A(x: int, y: real)
  | B(h: MyClass, x: int)
  | C(y: real)

class MyClass { }


datatype Klef =
  | C0(0: int, 1: int, 2: int, c0: int)
  | C1(1: int, 2: int, 3: int, c1: int)
  | C2(2: int, 3: int, 0: int, c2: int)
  | C3(3: int, 0: int, 1: int, c3: int)


datatype Datte<T> = AA(a: int, x: int) | BB(b: bool, x: int) | CC(c: real) | DD(x: int, o: set<int>, p: bv27, q: T)
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method Matte(d: Datte<real>)
  requires !d.CC?
// </vc-spec>
// <vc-code>
{
  var d := d;

  var s := d.(x := 5);
  print d, " ", s, "\n";  // AA(10, 2) AA(10, 5)

  d := BB(false, 12);
  s := d.(x := 6);
  print d, " ", s, "\n";  // BB(false, 12) BB(false, 6)

  d := CC(3.2);
  s := d.(c := 3.4);
  print d, " ", s, "\n";  // CC(3.2) CC(3.4)

  d := DD(100, {7}, 5, 9.0);
  s := d.(x := 30);
  print d, " ", s, "\n";  // DD(100, {7}, 5, 9.0) DD(30, {7}, 5, 9.0)
  s := s.(q := 2.0, p := d.p);
  print d, " ", s, "\n";  // DD(100, {7}, 5, 9.0) DD(30, {7}, 5, 2.0)
}
// </vc-code>
