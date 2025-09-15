// <vc-preamble>
function factorial_spec(n : int) : int
  requires n >= 0
  decreases n
{
  if n == 0 then 1 else n * factorial_spec(n - 1)
}
function sum_spec(n : int) : int
  requires n >= 0
  decreases n
{
  if n == 0 then 1 else n + sum_spec(n - 1)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method f(n : int) returns (result : seq<int>)

  requires n >= 1

  ensures |result| == n
  ensures forall i : int :: i >= 0 && i < |result| && i % 2 == 0 ==> result[i] == factorial_spec(i)
  ensures forall i : int :: i >= 0 && i < |result| && i % 2 != 0 ==> result[i] == sum_spec(i)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed invariant s[0 .. i] length to i, and strengthened loop invariants to ensure sequence construction correctness */
{
  var s: seq<int> := [];
  var i: int := 0;

  while i < n
    invariant 0 <= i <= n
    invariant |s| == i
    invariant forall k: int :: 0 <= k < i && k % 2 == 0 ==> s[k] == factorial_spec(k)
    invariant forall k: int :: 0 <= k < i && k % 2 != 0 ==> s[k] == sum_spec(k)
  {
    if i % 2 == 0 {
      s := s + [factorial_spec(i)];
    } else {
      s := s + [sum_spec(i)];
    }
    i := i + 1;
  }
  result := s;
}
// </vc-code>
