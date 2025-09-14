function sumInts( n: int ): int
    requires n >= 0;
{
    if n == 0 then
        0
    else
        sumInts(n-1)+n
}

// <vc-helpers>
function sumInts(n: int): int
  requires n >= 0
{
  if n == 0 then 0 else sumInts(n-1) + n
}

lemma SumInts_formula(n: int)
  requires n >= 0
  ensures sumInts(n) == n*(n+1)/2
  decreases n
{
  if n == 0 {
  } else {
    SumInts_formula(n-1)
    assert sumInts(n) == sumInts(n-1) + n
    assert sumInts(n-1) == (n-1)*n/2
    assert sumInts(n) == (n-1)*n/2 + n
    assert (n-1)*n/2 + n == n*(n+1)/2
  }
}

lemma SumInts_step(i: int)
  requires i >= 0
  ensures sumInts(i+1) == sumInts(i) + (i+1)
{
  SumInts_formula(i+1)
  SumInts_formula(i)
  assert sumInts(i+1) == (i+1)*(i+2)/2
  assert sumInts(i) == i*(i+1)/2
  assert (i+1)*(i+2)/2 == i*(i+1)/2 + (i+1)
}
// </vc-helpers>

// <vc-spec>
method SumIntsLoop( n: int ) returns ( s: int )
    requires n >= 0;
    ensures s == sumInts(n)
    ensures s == n*(n+1)/2;
// </vc-spec>
// <vc-code>
{
  var i := 0;
  s := 0;
  while i < n
    invariant 0 <= i <= n
    invariant s == sumInts(i)
  {
    var j := i + 1;
    SumInts_step(i);
    s := s + j;
    i := j;
  }
  SumInts_formula(n);
  assert s == sumInts(n);
  assert sumInts(n) == n*(n+1)/2;
}
// </vc-code>

