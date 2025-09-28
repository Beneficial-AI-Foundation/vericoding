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

/* helper modified by LLM (iteration 5): Removed redundant helper functions */

predicate ValidResultElement(i: nat, value: nat) {
    if (i + 1) % 2 == 0 then
        value == factorial(i + 1)
    else
        value == sum_range(i + 1)
}

// </vc-helpers>

// <vc-spec>
method f(n: nat) returns (result: seq<nat>)
    ensures ValidResult(n, result)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Simplified using sequence comprehension and eliminated loop invariants */
  result := seq(n, i requires 0 <= i < n => 
    if (i + 1) % 2 == 0 then factorial(i + 1) else sum_range(i + 1));
}
// </vc-code>
