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
lemma even_odd_factorial_sum(i: int, n: int)
  requires i >= 0 && i < n
  ensures (i % 2 == 0 ==> factorial_spec(i) >= 1)
  ensures (i % 2 != 0 ==> sum_spec(i) >= 1)
{
  if i % 2 == 0 {
    assert factorial_spec(i) >= 1;
  } else {
    assert sum_spec(i) >= 1;
  }
}

lemma monotonic_factorial(k: int)
  requires k >= 0
  ensures factorial_spec(k) >= 1
  decreases k
{
  if k == 0 {
  } else {
    monotonic_factorial(k - 1);
  }
}

lemma monotonic_sum(k: int)
  requires k >= 0
  ensures sum_spec(k) >= 1
  decreases k
{
  if k == 0 {
  } else {
    monotonic_sum(k - 1);
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
  result := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |result| == i
    invariant forall j : int :: j >= 0 && j < i && j % 2 == 0 ==> result[j] == factorial_spec(j)
    invariant forall j : int :: j >= 0 && j < i && j % 2 != 0 ==> result[j] == sum_spec(j)
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

