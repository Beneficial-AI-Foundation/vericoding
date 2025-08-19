//ATOM
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
  k := 0;
  assume i <= k <= j;
  assume forall r | i <= r < k :: a[r] >= x;
  assume forall r | k <= r < j :: a[r] < x;
  return k;
}


//ATOM

method SearchLoop( a: seq<real>, i: int, j: int, x: real ) returns ( k: int )
  requires 0 <= i <= j <= |a|
  requires forall p, q :: i <= p < q < j ==> a[p] >= a[q]
  ensures i <= k <= j
  ensures forall r | i <= r < k :: a[r] >= x
  ensures forall r | k <= r < j :: a[r] < x
{
  k := 0;
  assume i <= k <= j;
  assume forall r | i <= r < k :: a[r] >= x;
  assume forall r | k <= r < j :: a[r] < x;
  return k;
}


//IMPL Test

// Ef eftirfarandi fall er ekki samþykkt þá eru
// föllin ekki að haga sér rétt að mati Dafny.
method Test( a: seq<real>, x: real )
  requires forall p,q | 0 <= p < q < |a| :: a[p] >= a[q]
{
  /* code modified by LLM (iteration 1): Implemented proper calls to search methods with correct preconditions */
  var k1 := SearchRecursive(a, 0, |a|, x);
  var k2 := SearchLoop(a, 0, |a|, x);
}