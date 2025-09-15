// <vc-preamble>
function fibfib(n: nat): nat
  decreases n
{
  if n == 0 || n == 1 then 0
  else if n == 2 then 1
  else fibfib(n - 1) + fibfib(n - 2) + fibfib(n - 3)
}
// </vc-preamble>

// <vc-helpers>
lemma FibFibLemma(n: nat)
  ensures fibfib(n) >= 0
  decreases n
{
  if n == 0 || n == 1 {
  } else if n == 2 {
  } else {
    FibFibLemma(n - 1);
    FibFibLemma(n - 2);
    FibFibLemma(n - 3);
  }
}
// </vc-helpers>

// <vc-spec>
method ComputeFibFib(n: nat) returns (result: nat)

  ensures result == fibfib(n)
// </vc-spec>
// <vc-code>
{
  if n == 0 || n == 1 {
    result := 0;
  } else if n == 2 {
    result := 1;
  } else {
    var a := ComputeFibFib(n - 1);
    var b := ComputeFibFib(n - 2);
    var c := ComputeFibFib(n - 3);
    result := a + b + c;
    FibFibLemma(n - 1);
    FibFibLemma(n - 2);
    FibFibLemma(n - 3);
  }
}
// </vc-code>
