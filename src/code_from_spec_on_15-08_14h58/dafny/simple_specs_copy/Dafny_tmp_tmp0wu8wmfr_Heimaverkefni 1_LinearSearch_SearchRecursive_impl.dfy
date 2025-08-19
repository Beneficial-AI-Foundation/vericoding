// IMPL
// Author of question: Snorri Agnarsson
// Permalink of question: https://rise4fun.com/Dafny/0HRr

// Author of solution:  Alexander Guðmundsson
// Permalink of solution: https://rise4fun.com/Dafny/8pxWd

// Use the command
//  dafny LinearSearch-skeleton.dfy
// or
//  compile LinearSearch-skeleton.dfy
// to compile the file.
// Or use the web page rise4fun.com/dafny.

// When you have solved the problem put
// the solution on the Dafny web page,
// generate a permalink and put it in
// this file.



method SearchRecursive( a: seq<int>, i: int, j: int, x: int ) returns (k: int)
  requires 0 <= i <= j <= |a|
  ensures i <= k < j || k == -1
  ensures k != -1 ==> a[k] == x
  ensures k != -1 ==> forall r | k < r < j :: a[r] != x
  ensures k == -1 ==> forall r | i <= r < j :: a[r] != x
  /* code modified by LLM (iteration 1): added decreases clause for termination */
  decreases j - i
{
  if i >= j {
    k := -1;
  } else if a[i] == x {
    /* code modified by LLM (iteration 1): search rest of array to find last occurrence */
    var rest := SearchRecursive(a, i + 1, j, x);
    if rest == -1 {
      k := i;
    } else {
      k := rest;
    }
  } else {
    k := SearchRecursive(a, i + 1, j, x);
  }
}