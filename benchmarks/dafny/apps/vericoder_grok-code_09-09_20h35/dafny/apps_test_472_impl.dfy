function digitSum(n: int): int
  requires n >= 0
  decreases n
{
  if n == 0 then 0
  else (n % 10) + digitSum(n / 10)
}

// <vc-helpers>
lemma NoLargeX(n: int)
  requires n >= 1
  ensures forall x :: x > 0 && x > n ==> x * (x + digitSum(x)) != n
{
  forall x | x > 0 && x > n
  {
    var ds := digitSum(x);
    assert n >= 1;
    assert (n + 1) * (n + 1) > n;
    assert x >= n + 1;
    assert ds >= 0;
    assert x + ds >= x > n;
    assert x * (x + ds) >= (n + 1) * (n + 1) > n;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
  requires n >= 1
  ensures n == 1 ==> result == -1
  ensures n > 1 && result > 0 ==> result * result + digitSum(result) * result == n
  ensures n > 1 && result > 0 ==> forall y :: y > 0 && y < result ==> y * y + digitSum(y) * y != n
  ensures n > 1 && result == -1 ==> forall x :: x > 0 ==> x * x + digitSum(x) * x != n
  ensures result == -1 || result > 0
// </vc-spec>
// <vc-code>
{
  if n == 1 {
    return -1;
  }
  var i := 1;
  while i <= n + 1
    decreases n + 1 - i
    invariant 1 <= i <= n + 2
    invariant forall y :: 1 <= y < i ==> y * (y + digitSum(y)) != n
  {
    var ds := digitSum(i);
    var prod := i * (i + ds);
    if prod == n {
      return i;
    }
    i := i + 1;
  }
  NoLargeX(n);
  return -1;
}
// </vc-code>

