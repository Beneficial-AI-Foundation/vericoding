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
lemma SeqProperties(a: seq<int>, i: int, j: int, x: int)
  requires 0 <= i <= j <= |a|
  ensures forall r | i <= r < j :: r < |a|
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method SearchRecursive( a: seq<int>, i: int, j: int, x: int ) returns (k: int)
    decreases j-i;
    requires 0 <= i <= j <= |a|;
    ensures i <= k < j || k == -1;
    ensures k != -1 ==> a[k] == x;
    ensures k != -1 ==> forall r | k < r < j :: a[r] != x;
    ensures k == -1 ==> forall r | i <= r < j :: a[r] != x;
// </vc-spec>
// </vc-spec>

// <vc-code>
method SearchRecursiveImpl(a: seq<int>, i: int, j: int, x: int) returns (k: int)
  decreases j - i
  requires 0 <= i <= j <= |a|
  ensures i <= k < j || k == -1
  ensures k != -1 ==> a[k] == x
  ensures k != -1 ==> forall r | k < r < j :: a[r] != x
  ensures k == -1 ==> forall r | i <= r < j :: a[r] != x
{
  if i == j {
    k := -1;
    return;
  }
  
  var mid := (i + j) / 2;
  
  if a[mid] == x {
    k := mid;
    return;
  }
  
  if a[mid] > x {
    k := SearchRecursiveImpl(a, i, mid, x);
  } else {
    k := SearchRecursiveImpl(a, mid + 1, j, x);
    if k != -1 {
      assert k > mid;
    }
  }
}
// </vc-code>
