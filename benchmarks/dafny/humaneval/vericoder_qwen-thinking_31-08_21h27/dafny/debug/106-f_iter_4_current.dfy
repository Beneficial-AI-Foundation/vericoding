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
result := new seq<int>(n);
for i := 0 to n - 1
  invariant |result| == n
  invariant forall k : int | 0 <= k && k < i :: result[k] == (if k % 2 == 0 then factorial_spec(k) else sum_spec(k))
{
    if i % 2 == 0 {
        result[i] := factorial_spec(i);
    } else {
        result[i] := sum_spec(i);
    }
}
// </vc-code>

