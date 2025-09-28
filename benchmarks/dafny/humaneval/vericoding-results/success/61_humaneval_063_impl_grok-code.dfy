// <vc-preamble>

function fibfib_spec(n: int): int
    requires n >= 0
{
    if n == 0 then 0
    else if n == 1 then 0
    else if n == 2 then 1
    else fibfib_spec(n-1) + fibfib_spec(n-2) + fibfib_spec(n-3)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method fibfib(n: int) returns (result: int)
    requires n >= 0
    ensures result == fibfib_spec(n)
    ensures n == 0 ==> result == 0
    ensures n == 1 ==> result == 0
    ensures n == 2 ==> result == 1
    ensures n >= 3 ==> result == fibfib_spec(n-1) + fibfib_spec(n-2) + fibfib_spec(n-3)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Iterative implementation with loop invariants to ensure correctness against fibfib_spec */
{
  if n == 0 {
    result := 0;
  } else if n == 1 {
    result := 0;
  } else if n == 2 {
    result := 1;
  } else {
    var prev3 := 0;
    var prev2 := 0;
    var prev1 := 1;
    var i := 3;
    while i <= n
      invariant 3 <= i <= n + 1
      invariant fibfib_spec(i - 1) == prev1
      invariant fibfib_spec(i - 2) == prev2
      invariant fibfib_spec(i - 3) == prev3
    {
      var next := prev3 + prev2 + prev1;
      prev3 := prev2;
      prev2 := prev1;
      prev1 := next;
      i := i + 1;
    }
    result := prev1;
  }
}
// </vc-code>
