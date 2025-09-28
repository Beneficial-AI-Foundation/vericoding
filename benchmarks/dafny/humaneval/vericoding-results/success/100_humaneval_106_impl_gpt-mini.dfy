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
lemma ZeroNonneg() ensures 0 >= 0 {
}

// </vc-helpers>

// <vc-spec>
method f(n: nat) returns (result: seq<nat>)
    ensures ValidResult(n, result)
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    result := [];
  } else {
    var tail := f(n - 1);
    var last := if n % 2 == 0 then factorial(n) else sum_range(n);
    result := tail + [last];
  }
}

// </vc-code>
