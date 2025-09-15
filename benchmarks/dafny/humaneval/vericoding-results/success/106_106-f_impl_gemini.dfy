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
  result := [];
  var i := 0;
  var fact: int := 1;
  var sum: int := 1;

  while(i < n)
    invariant 0 <= i <= n
    invariant |result| == i
    invariant fact == factorial_spec(i)
    invariant sum == sum_spec(i)
    invariant forall k :: 0 <= k < i && k % 2 == 0 ==> result[k] == factorial_spec(k)
    invariant forall k :: 0 <= k < i && k % 2 != 0 ==> result[k] == sum_spec(k)
  {
      if i % 2 == 0 {
          result := result + [fact];
      } else {
          result := result + [sum];
      }
      i := i + 1;
      if i > 0 {
        fact := fact * i;
        sum := sum + i;
      }
  }
}
// </vc-code>
