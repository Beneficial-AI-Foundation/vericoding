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
lemma factorial_property(n: int)
  requires n >= 0
  ensures factorial_spec(n) >= 1
{
  if n == 0 {
    assert factorial_spec(0) == 1;
  } else {
    factorial_property(n - 1);
    assert factorial_spec(n) == n * factorial_spec(n - 1);
    assert factorial_spec(n - 1) >= 1;
    assert n >= 1;
    assert factorial_spec(n) >= 1;
  }
}

lemma sum_property(n: int)
  requires n >= 0
  ensures sum_spec(n) >= 1
{
  if n == 0 {
    assert sum_spec(0) == 1;
  } else {
    sum_property(n - 1);
    assert sum_spec(n) == n + sum_spec(n - 1);
    assert sum_spec(n - 1) >= 1;
    assert n >= 1;
    assert sum_spec(n) >= 1;
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
    invariant forall j : int :: j >= 0 && j < |result| && j % 2 == 0 ==> result[j] == factorial_spec(j)
    invariant forall j : int :: j >= 0 && j < |result| && j % 2 != 0 ==> result[j] == sum_spec(j)
  {
    var value: int;
    if i % 2 == 0 {
      value := factorial_spec(i);
    } else {
      value := sum_spec(i);
    }
    result := result + [value];
    i := i + 1;
  }
}
// </vc-code>

