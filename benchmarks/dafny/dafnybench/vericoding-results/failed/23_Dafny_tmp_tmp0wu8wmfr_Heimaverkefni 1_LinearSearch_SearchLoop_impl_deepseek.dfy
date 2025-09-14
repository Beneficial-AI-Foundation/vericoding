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
lemma SearchLoopLemma(a: seq<int>, i: int, j: int, x: int, k: int)
  requires 0 <= i <= j <= |a|
  requires i <= k < j && a[k] == x
  requires forall r | k < r < j :: a[r] != x
  ensures forall r | i <= r < j :: a[r] != x || (exists s | r <= s < j :: a[s] == x)
{
  var r : int := i;
  while r < j
    invariant i <= r <= j
    invariant forall t | i <= t < r :: a[t] != x || (exists s | t <= s < j :: a[s] == x)
  {
    if r <= k {
      assert exists s | r <= s < j :: a[s] == x;
    } else {
      assert a[r] != x;
    }
    r := r + 1;
  }
}
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
  var index := i;
  k := -1;
  
  while index < j
    invariant i <= index <= j
    invariant k == -1 || (i <= k < j && a[k] == x)
    invariant k == -1 ==> forall r | i <= r < index :: a[r] != x
    invariant k != -1 ==> forall r | k < r < j :: a[r] != x
  {
    if a[index] == x {
      k := index;
      break;
    }
    index := index + 1;
  }
  
  if k != -1 {
    // The lemma call is no longer needed since we maintain the invariant
    // SearchLoopLemma(a, i, j, x, k);
  }
}
// </vc-code>

