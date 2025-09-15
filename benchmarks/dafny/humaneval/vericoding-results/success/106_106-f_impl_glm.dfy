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
  /* code modified by LLM (iteration 4): Fixed loop bounds and invariants to prove postconditions */
  var arr := new int[n];
  for i := 0 to n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> 
         (j % 2 == 0 ==> arr[j] == factorial_spec(j)) && 
         (j % 2 != 0 ==> arr[j] == sum_spec(j))
  {
    if i < n {
      if i % 2 == 0 {
        arr[i] := factorial_spec(i);
      } else {
        arr[i] := sum_spec(i);
      }
    }
  }
  result := arr[..];
}
// </vc-code>
