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
lemma FactorialAndSumNonNegative(n: int)
  requires n >= 0
  ensures factorial_spec(n) > 0
  ensures sum_spec(n) > 0
{
  if n == 0 {
    assert factorial_spec(0) == 1;
    assert sum_spec(0) == 1;
  } else {
    FactorialAndSumNonNegative(n - 1);
    assert factorial_spec(n) == n * factorial_spec(n - 1);
    assert sum_spec(n) == n + sum_spec(n - 1);
  }
}
// </vc-helpers>

// <vc-spec>
method f(n : int) returns (result : seq<int>)
  // pre-conditions-start
  requires n >= 1
  // pre-conditions-end
  // post-conditions-start
  ensures |result| == n
  ensures forall i : int :: i >= 0 && i < |result| && i % 2 == 0 ==> result[i] == factorial_spec(i)
  ensures forall i : int :: i >= 0 && i < |result| && i % 2 != 0 ==> result[i] == sum_spec(i)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var seqResult: seq<int> := [];
  var i: int := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant |seqResult| == i
    invariant forall k: int :: 0 <= k < i && k % 2 == 0 ==> seqResult[k] == factorial_spec(k)
    invariant forall k: int :: 0 <= k < i && k % 2 != 0 ==> seqResult[k] == sum_spec(k)
  {
    if i % 2 == 0 {
      seqResult := seqResult + [factorial_spec(i)];
    } else {
      seqResult := seqResult + [sum_spec(i)];
    }
    i := i + 1;
  }
  
  result := seqResult;
}
// </vc-code>
