function fibfib(n: nat): nat
  decreases n
{
  if n == 0 || n == 1 then 0
  else if n == 2 then 1
  else fibfib(n - 1) + fibfib(n - 2) + fibfib(n - 3)
}

// <vc-helpers>
lemma FibFibNonNegative(n: nat)
  ensures fibfib(n) >= 0
{
  if n == 0 || n == 1 {
    assert fibfib(n) == 0;
  } else if n == 2 {
    assert fibfib(n) == 1;
  } else {
    calc {
      fibfib(n);
      fibfib(n-1) + fibfib(n-2) + fibfib(n-3);
      >= { FibFibNonNegative(n-1); FibFibNonNegative(n-2); FibFibNonNegative(n-3); }
      0 + 0 + 0;
      0;
    }
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def fibfib(n: int)
The FibFib number sequence is a sequence similar to the Fibbonacci sequnece that's defined as follows: fibfib(0) == 0 fibfib(1) == 0 fibfib(2) == 1 fibfib(n) == fibfib(n-1) + fibfib(n-2) + fibfib(n-3). Please write a function to efficiently compute the n-th element of the fibfib number sequence. Note(Meghana): While the specification asks for an efficient computation of fibfib, we cannot enforce this constraint currently.
*/
// </vc-description>

// <vc-spec>
method ComputeFibFib(n: nat) returns (result: nat)
  ensures result == fibfib(n)
// </vc-spec>
// <vc-code>
{
  if n == 0 || n == 1 {
    return 0;
  } else if n == 2 {
    return 1;
  } else {
    var a := 0;
    var b := 0;
    var c := 1;
    var i := 2;
    while i < n
      invariant 0 <= i <= n
      invariant a == fibfib(i-2)
      invariant b == fibfib(i-1)
      invariant c == fibfib(i)
    {
      var next := a + b + c;
      a := b;
      b := c;
      c := next;
      i := i + 1;
    }
    return c;
  }
}
// </vc-code>
