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
/* no helpers needed */
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

