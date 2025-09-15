// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
function factorial(n: int): int
  requires n >= 0
  decreases n
{
  if n == 0 then 1 else n * factorial(n - 1)
}

function sum(n: int): int
  requires n >= 0
  decreases n
{
  if n == 0 then 1 else n + sum(n - 1)
}

lemma factorial_equiv(n: int)
  requires n >= 0
  ensures factorial(n) == factorial_spec(n)
  decreases n
{
  if n == 0 {
  } else {
    factorial_equiv(n - 1);
  }
}

lemma sum_equiv(n: int)
  requires n >= 0
  ensures sum(n) == sum_spec(n)
  decreases n
{
  if n == 0 {
  } else {
    sum_equiv(n - 1);
  }
}
// </vc-helpers>

// <vc-spec>
method f(n : int) returns (result : seq<int>)

  requires n >= 1

  ensures |result| == n
  ensures forall i : int :: i >= 0 && i < |result| && i % 2 == 0 ==> result[i] == factorial_spec(i)
  ensures forall i : int :: i >= 0 && i < |result| && i % 2 != 0 ==> result[i] == sum_spec(i)
// </vc-spec>
// <vc-code>
{
  result := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |result| == i
    invariant forall j :: 0 <= j < i && j % 2 == 0 ==> result[j] == factorial_spec(j)
    invariant forall j :: 0 <= j < i && j % 2 != 0 ==> result[j] == sum_spec(j)
  {
    if i % 2 == 0 {
      factorial_equiv(i);
      result := result + [factorial(i)];
    } else {
      sum_equiv(i);
      result := result + [sum(i)];
    }
    i := i + 1;
  }
}
// </vc-code>
