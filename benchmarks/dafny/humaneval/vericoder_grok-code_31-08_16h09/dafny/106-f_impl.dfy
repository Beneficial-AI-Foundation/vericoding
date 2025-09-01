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
// No updates needed
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
  result := [];
  var i := 0;
  while i < n 
    invariant 0 <= i <= n
    invariant |result| == i
    invariant forall k :: 0 <= k < i && k % 2 == 0 ==> result[k] == factorial_spec(k)
    invariant forall k :: 0 <= k < i && k % 2 != 0 ==> result[k] == sum_spec(k)
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

