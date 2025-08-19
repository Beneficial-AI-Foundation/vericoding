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
{
  if i >= j {
    k := -1;
  } else {
    /* code modified by LLM (iteration 1): Search recursively in the right part first to find rightmost occurrence */
    k := SearchRecursive(a, i + 1, j, x);
    /* code modified by LLM (iteration 1): If no occurrence found in right part and current element matches, return current position */
    if k == -1 && a[i] == x {
      k := i;
    }
    /* code modified by LLM (iteration 1): If occurrence found in right part, keep it regardless of current element since we want rightmost */
  }
}