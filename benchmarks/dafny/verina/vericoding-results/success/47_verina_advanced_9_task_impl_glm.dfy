// <vc-preamble>
function SumOfDigits(x: nat): nat
    decreases x
{
    if x == 0 then 0 else (x % 10) + SumOfDigits(x / 10)
}

predicate IsSumDivisibleBy(x: nat, d: nat)
    requires d > 0
{
    (SumOfDigits(x) % d) == 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method CountSumDivisibleBy(n: nat, d: nat) returns (result: nat)
    requires d > 0
    ensures result <= n
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): fixed loop invariant to be maintained */
  var count := 0;
  for x := 0 to n
    invariant count <= x
  {
    if x > 0 && IsSumDivisibleBy(x-1, d) {
      count := count + 1;
    }
  }
  result := count;
}
// </vc-code>
