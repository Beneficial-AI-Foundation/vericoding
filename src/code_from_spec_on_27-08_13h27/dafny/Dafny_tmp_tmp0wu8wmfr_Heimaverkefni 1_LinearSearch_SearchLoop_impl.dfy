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
// Helper lemma to assist in proving properties if needed
lemma SeqProperty(a: seq<int>, i: int, j: int, x: int)
  ensures true
{
  // Empty lemma body as no additional properties need to be proven for this implementation
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method SearchLoop( a: seq<int>, i: int, j: int, x: int ) returns (k: int)
    requires 0 <= i <= j <= |a|;
    ensures i <= k < j || k == -1;
    ensures k != -1 ==> a[k] == x;
    ensures k != -1 ==> forall r | k < r < j :: a[r] != x;
    ensures k == -1 ==> forall r | i <= r < j :: a[r] != x;
// </vc-spec>
// </vc-spec>

// <vc-code>
method SearchLoopImpl(a: seq<int>, i: int, j: int, x: int) returns (k: int)
  requires 0 <= i <= j <= |a|
  ensures i <= k < j || k == -1
  ensures k != -1 ==> a[k] == x
  ensures k != -1 ==> forall r | k < r < j :: a[r] != x
  ensures k == -1 ==> forall r | i <= r < j :: a[r] != x
{
  k := -1;
  var r := i;
  while r < j
    invariant i <= r <= j
    invariant k == -1 ==> forall s | i <= s < r :: a[s] != x
    invariant k != -1 ==> i <= k < r && a[k] == x && forall s | k < s < r :: a[s] != x
  {
    if a[r] == x
    {
      k := r;
    }
    r := r + 1;
  }
}
// </vc-code>
