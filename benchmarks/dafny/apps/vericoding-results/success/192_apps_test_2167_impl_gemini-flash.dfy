// <vc-preamble>
predicate ValidInput(n: int, arr: seq<int>)
{
  n >= 1 && |arr| == n
}

function sum_seq(s: seq<int>): int
{
  if |s| == 0 then 0
  else s[0] + sum_seq(s[1..])
}

predicate CorrectResult(n: int, arr: seq<int>, result: int)
  requires ValidInput(n, arr)
{
  (sum_seq(arr) % n == 0 ==> result == n) &&
  (sum_seq(arr) % n != 0 ==> result == n - 1) &&
  (result == n || result == n - 1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added precondition for n to ensure no division by zero */
function ComputeResult(n: int, arr: seq<int>): int
  requires n != 0
{
  if sum_seq(arr) % n == 0 then n else n - 1
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, arr: seq<int>) returns (result: int)
  requires ValidInput(n, arr)
  ensures CorrectResult(n, arr, result)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): calling ComputeResult with valid n ensured by method precondition */
{
  result := ComputeResult(n, arr);
}
// </vc-code>
