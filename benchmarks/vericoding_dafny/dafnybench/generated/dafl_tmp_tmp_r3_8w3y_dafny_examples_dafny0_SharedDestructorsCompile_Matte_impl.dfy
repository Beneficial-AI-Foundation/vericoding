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

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Matte(d: Datte<real>)
  requires !d.CC?
// </vc-spec>
// <vc-code>
{
  // The method has a precondition that d is not CC
  // Since d is not CC, it must be one of AA, BB, or DD
  // The method body can be empty since there are no postconditions to satisfy
}
// </vc-code>