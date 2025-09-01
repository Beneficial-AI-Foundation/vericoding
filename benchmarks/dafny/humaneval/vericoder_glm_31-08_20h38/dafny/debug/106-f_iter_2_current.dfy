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
lemma factorial_spec_positive(n: int)
  requires n >= 0
  ensures factorial_spec(n) >= 1
{
  if n != 0 {
    calc {
      factorial_spec(n);
      n * factorial_spec(n - 1);
      >=  1 * 1;
      ==    1;
    }
  }
}

lemma sum_spec_positive(n: int)
  requires n >= 0
  ensures sum_spec(n) >= 1
{
  if n != 0 {
    calc {
      sum_spec(n);
      n + sum_spec(n - 1);
      >=  1 + 1;
      >     1;
    }
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
  var s := new int[n];
  for i := 0 to n
    invariant 0 <= i <= n
    invariant forall j : int :: j >= 0 && j < i && j % 2 == 0 ==> s[j] == factorial_spec(j)
    invariant forall j : int :: j >= 0 && j < i && j % 2 != 0 ==> s[j] == sum_spec(j)
  {
    if i % 2 == 0 {
      s[i] := factorial_spec(i);
      factorial_spec_positive(i);
    } else {
      s[i] := sum_spec(i);
      sum_spec_positive(i);
    }
  }
  result := s[..];
}
// </vc-code>

