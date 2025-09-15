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
{
  /* code modified by LLM (iteration 3): Used while loop with invariants to ensure |result| == n and all elements match specifications */
  result := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |result| == i
    invariant forall j :: 0 <= j < i && j % 2 == 0 ==> result[j] == factorial_spec(j)
    invariant forall j :: 0 <= j < i && j % 2 != 0 ==> result[j] == sum_spec(j)
  {
    if i % 2 == 0 {
      result := result + [factorial_spec(i)];
    } else {
      result := result + [sum_spec(i)];
    }
    i := i + 1;
  }
}
// </vc-code>
