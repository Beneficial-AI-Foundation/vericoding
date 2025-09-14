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
{
  var res := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |res| == i
    invariant forall j :: j >= 0 && j < |res| && j % 2 == 0 ==> res[j] == factorial_spec(j)
    invariant forall j :: j >= 0 && j < |res| && j % 2 != 0 ==> res[j] == sum_spec(j)
    decreases n - i
  {
    if i % 2 == 0 {
      res := res + [factorial_spec(i)];
    } else {
      res := res + [sum_spec(i)];
    }
    i := i + 1;
  }
  result := res;
}
// </vc-code>

