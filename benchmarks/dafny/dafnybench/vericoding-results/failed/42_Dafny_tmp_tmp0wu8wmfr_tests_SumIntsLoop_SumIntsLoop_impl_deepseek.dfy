function sumInts( n: int ): int
    requires n >= 0;
{
    if n == 0 then
        0
    else
        sumInts(n-1)+n
}

// <vc-helpers>
lemma sumIntsFormula(n: int)
  requires n >= 0
  ensures sumInts(n) == n * (n + 1) / 2
{
  if n == 0 {
    assert sumInts(0) == 0;
  } else {
    sumIntsFormula(n - 1);
    assert sumInts(n) == sumInts(n - 1) + n;
  }
}

lemma sumIntsZero()
  ensures sumInts(0) == 0
{
}

lemma sumIntsNonNegative(n: int)
  requires n >= 0
  ensures sumInts(n) >= 0
{
  if n == 0 {
  } else {
    sumIntsNonNegative(n - 1);
  }
}

lemma sumIntsRecurrence(n: int)
  requires n > 0
  ensures sumInts(n) == sumInts(n - 1) + n
{
}

lemma sumIntsBaseCase()
  ensures sumInts(0) == 0
{
}

lemma sumIntsStepCase(n: int)
  requires n > 0
  requires sumInts(n - 1) == (n - 1) * n / 2
  ensures sumInts(n) == n * (n + 1) / 2
{
  sumIntsRecurrence(n);
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method SumIntsLoop( n: int ) returns ( s: int )
    requires n >= 0;
    ensures s == sumInts(n)
    ensures s == n*(n+1)/2;
// </vc-spec>
// <vc-code>
{
  s := 0;
  var i := 0;
  while i <= n
    invariant 0 <= i <= n + 1
    invariant s == sumInts(i)
  {
    s := s + i;
    i := i + 1;
  }
  sumIntsFormula(n);
}
// </vc-code>

