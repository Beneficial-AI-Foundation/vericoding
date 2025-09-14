// Author of question: Snorri Agnarsson
// Permalink of question: https://rise4fun.com/Dafny/0HRr

// Author of solution:    Alexander Guðmundsson
// Permalink of solution: https://rise4fun.com/Dafny/8pxWd

// Use the command
//   dafny LinearSearch-skeleton.dfy
// or
//   compile LinearSearch-skeleton.dfy
// to compile the file.
// Or use the web page rise4fun.com/dafny.

// When you have solved the problem put
// the solution on the Dafny web page,
// generate a permalink and put it in
// this file.

// <vc-helpers>
method SearchLoop( a: seq<int>, i: int, j: int, x: int ) returns (k: int)
    requires 0 <= i <= j <= |a|
    ensures i <= k < j || k == -1
    ensures k != -1 ==> a[k] == x
    ensures k != -1 ==> forall r | k < r < j :: a[r] != x
    ensures k == -1 ==> forall r | i <= r < j :: a[r] != x
// </vc-helpers>

// <vc-spec>
method SearchLoop( a: seq<int>, i: int, j: int, x: int ) returns (k: int)
    requires 0 <= i <= j <= |a|;
    ensures i <= k < j || k == -1;
    ensures k != -1 ==> a[k] == x;
    ensures k != -1 ==> forall r | k < r < j :: a[r] != x;
    ensures k == -1 ==> forall r | i <= r < j :: a[r] != x;
// </vc-spec>
// <vc-code>
{
  k := -1;
  var m: int := i;
  while m < j
    invariant i <= m <= j
    invariant k == -1 ==> forall r | i <= r < m :: a[r] != x
    invariant k != -1 ==> i <= k < m && a[k] == x
    invariant k != -1 ==> forall r | k < r < m :: a[r] != x
  {
    if a[m] == x {
      k := m;
    }
    m := m + 1;
  }
  return k;
}
// </vc-code>

