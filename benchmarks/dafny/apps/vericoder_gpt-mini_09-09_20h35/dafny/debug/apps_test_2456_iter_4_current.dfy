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
lemma ExpectedResult_unfold(n: int, r: int)
  requires ValidInput(n, r)
  ensures ExpectedResult(n, r) == (let k := if r < n - 1 then r else n - 1 in k * (k + 1) / 2 + (if r >= n then 1 else 0))
{
  // By definition of the function ExpectedResult, the equality holds.
}
// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
{
  var k := if r < n - 1 then r else n - 1;
  var res := k * (k + 1) / 2 + (if r >= n then 1 else 0);
  return res;
}
// </vc-code>

