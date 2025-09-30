// <vc-preamble>

function factorial(n: nat): nat
{
    if n <= 1 then 1 else n * factorial(n - 1)
}

function sum_range(n: nat): nat
{
    if n == 0 then 0 else n + sum_range(n - 1)
}

predicate ValidResult(n: nat, result: seq<nat>)
{
    |result| == n &&
    forall i :: 0 <= i < n ==> 
        (if (i + 1) % 2 == 0 then result[i] == factorial(i + 1)
         else result[i] == sum_range(i + 1))
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method f(n: nat) returns (result: seq<nat>)
    ensures ValidResult(n, result)
// </vc-spec>
// <vc-code>
{
  result := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> 
      (if (j + 1) % 2 == 0 then result[j] == factorial(j + 1)
       else result[j] == sum_range(j + 1))
  {
    if (i + 1) % 2 == 0 {
      result := result + [factorial(i + 1)];
    } else {
      result := result + [sum_range(i + 1)];
    }
    i := i + 1;
  }
}
// </vc-code>
