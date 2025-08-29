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

// <vc-helpers>
// Helper lemma to ensure factorial_spec behaves correctly for verification
lemma FactorialPositive(n: int)
  requires n >= 0
  ensures factorial_spec(n) > 0
{
  if n == 0 {
    assert factorial_spec(0) == 1 > 0;
  } else {
    FactorialPositive(n - 1);
    assert factorial_spec(n) == n * factorial_spec(n - 1);
    assert factorial_spec(n) > 0;
  }
}

// Helper lemma to ensure sum_spec behaves correctly for verification
lemma SumPositive(n: int)
  requires n >= 0
  ensures sum_spec(n) > 0
{
  if n == 0 {
    assert sum_spec(0) == 1 > 0;
  } else {
    SumPositive(n - 1);
    assert sum_spec(n) == n + sum_spec(n - 1);
    assert sum_spec(n) > 0;
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def f(n: int) -> List[int]
Implement the function f that takes n as a parameter, and returns a list of size n, such that the value of the element at index i is the factorial of i if i is even or the sum of numbers from 1 to i otherwise. i starts from 1. the factorial of i is the multiplication of the numbers from 1 to i (1 * 2 * ... * i).
*/
// </vc-description>

// <vc-spec>
method f(n: int) returns (result: seq<int>)
  requires n >= 0
  ensures |result| == n
  ensures forall i :: 0 <= i < n ==> result[i] == (if (i + 1) % 2 == 0 then factorial_spec(i + 1) else sum_spec(i + 1))
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    return [];
  } else {
    var res: seq<int> := [];
    var i := 1;
    while i <= n
      invariant 0 <= i <= n + 1
      invariant |res| == i - 1
      invariant forall k :: 0 <= k < i - 1 ==> res[k] == (if (k + 1) % 2 == 0 then factorial_spec(k + 1) else sum_spec(k + 1))
    {
      var value := if i % 2 == 0 then factorial_spec(i) else sum_spec(i);
      res := res + [value];
      i := i + 1;
    }
    return res;
  }
}
// </vc-code>
