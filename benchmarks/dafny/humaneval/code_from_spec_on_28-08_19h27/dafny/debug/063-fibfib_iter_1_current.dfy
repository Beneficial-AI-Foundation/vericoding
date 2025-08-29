function fibfib(n: nat): nat
  decreases n
{
  if n == 0 || n == 1 then 0
  else if n == 2 then 1
  else fibfib(n - 1) + fibfib(n - 2) + fibfib(n - 3)
}

// <vc-helpers>
lemma FibfibCorrectness(n: nat)
  ensures fibfib(n) >= 0
{
  // This lemma helps establish that fibfib always returns non-negative values
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def fibfib(n: int)
The FibFib number sequence is a sequence similar to the Fibbonacci sequnece that's defined as follows: fibfib(0) == 0 fibfib(1) == 0 fibfib(2) == 1 fibfib(n) == fibfib(n-1) + fibfib(n-2) + fibfib(n-3). Please write a function to efficiently compute the n-th element of the fibfib number sequence. Note(Meghana): While the specification asks for an efficient computation of fibfib, we cannot enforce this constraint currently.
*/
// </vc-description>

// <vc-spec>
method fibfib_iterative(n: nat) returns (result: nat)
  ensures result == fibfib(n)
// </vc-spec>
// <vc-code>
{
  if n == 0 || n == 1 {
    result := 0;
  } else if n == 2 {
    result := 1;
  } else {
    var a, b, c := 0, 0, 1;
    var i := 3;
    while i <= n
      invariant 3 <= i <= n + 1
      invariant a == fibfib(i - 3)
      invariant b == fibfib(i - 2)
      invariant c == fibfib(i - 1)
    {
      var next := a + b + c;
      a, b, c := b, c, next;
      i := i + 1;
    }
    result := c;
  }
}
// </vc-code>
