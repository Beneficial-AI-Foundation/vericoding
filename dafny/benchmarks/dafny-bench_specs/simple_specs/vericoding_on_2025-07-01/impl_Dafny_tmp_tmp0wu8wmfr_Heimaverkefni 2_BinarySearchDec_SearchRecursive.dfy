// IMPL
// Author of question: Snorri Agnarsson
// Permalink of question: https://rise4fun.com/Dafny/CGB1z

// Authors of solution:  Alexander Guðmundsson
// Permalink of solution: https://rise4fun.com/Dafny/VnB5

// Use the command
//  dafny H2-skeleton.dfy
// or
//  compile H2-skeleton.dfy
// to compile the file.
// Or use the web page rise4fun.com/dafny.

// When you have solved the problem put
// the solution on the Dafny web page,
// generate a permalink and put it in
// this file.

method SearchRecursive( a: seq<real>, i: int, j: int, x: real ) returns ( k: int )
  requires 0 <= i <= j <= |a|
  requires forall p, q :: i <= p < q < j ==> a[p] >= a[q]
  ensures i <= k <= j
  ensures forall r | i <= r < k :: a[r] >= x
  ensures forall r | k <= r < j :: a[r] < x
{
  if i == j {
    k := i;
  } else if a[i] < x {
    k := i;
  } else {
    k := SearchRecursive(a, i + 1, j, x);
  }
}