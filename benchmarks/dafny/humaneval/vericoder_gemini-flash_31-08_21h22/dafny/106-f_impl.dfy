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
function factorial_helper(n : int) : int
  requires n >= 0
  decreases n
{
  if n == 0 then 1 else n * factorial_helper(n - 1)
}

function sum_helper(n : int) : int
  requires n >= 0
  decreases n
{
  if n == 0 then 0 else n + sum_helper(n - 1)
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
  var result_seq: seq<int> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |result_seq| == i
    invariant forall k : int :: 0 <= k < i && k % 2 == 0 ==> result_seq[k] == factorial_spec(k)
    invariant forall k : int :: 0 <= k < i && k % 2 != 0 ==> result_seq[k] == sum_spec(k)
  {
    if i % 2 == 0 {
      result_seq := result_seq + [factorial_spec(i)];
    } else {
      result_seq := result_seq + [sum_spec(i)];
    }
    i := i + 1;
  }
  return result_seq;
}
// </vc-code>

