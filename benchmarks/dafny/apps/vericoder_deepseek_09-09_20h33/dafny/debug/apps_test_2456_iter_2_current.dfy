predicate ValidInput(n: int, r: int)
{
    n >= 1 && r >= 1
}

function ExpectedResult(n: int, r: int): int
    requires ValidInput(n, r)
{
    var k := if r < n - 1 then r else n - 1;
    k * (k + 1) / 2 + (if r >= n then 1 else 0)
}

// <vc-helpers>
lemma SumOfFirstK(k: nat) returns (s: int)
  ensures s == k * (k + 1) / 2
{
  if k == 0 {
    s := 0;
  } else {
    var s' := SumOfFirstK(k - 1);
    s := s' + k;
  }
}

lemma ExpectedResultAlternative(n: int, r: int)
  requires ValidInput(n, r)
  ensures ExpectedResult(n, r) == 
    (if r < n - 1 then r * (r + 1) / 2 
     else if r >= n then (n - 1) * n / 2 + 1 
     else (n - 1) * n / 2)
{
}
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
{
  if r < n - 1 {
    var k := r;
    var sum := k * (k + 1) / 2;
    return sum;
  } else if r >= n {
    var k := n - 1;
    var sum := k * (k + 1) / 2 + 1;
    return sum;
  } else {
    var k := n - 1;
    var sum := k * (k + 1) / 2;
    return sum;
  }
}
// </vc-code>

