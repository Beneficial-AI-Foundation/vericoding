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

// </vc-helpers>

// <vc-spec>
method ComputeFibFib(n: nat) returns (result: nat)

  ensures result == fibfib(n)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): corrected if-else statement syntax */
{
  if n == 0 || n == 1 {
    result := 0;
  } else if n == 2 {
    result := 1;
  } else {
    var f1: nat;
    var f2: nat;
    var f3: nat;

    f1 := ComputeFibFib(n - 1);
    f2 := ComputeFibFib(n - 2);
    f3 := ComputeFibFib(n - 3);

    result := f1 + f2 + f3;
  }
}
// </vc-code>
