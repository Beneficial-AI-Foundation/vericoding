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

// </vc-helpers>

// <vc-spec>

// </vc-spec>
// <vc-code>
method compute(n: int, r: int) returns (result: int)
  requires ValidInput(n, r)
  ensures result == ExpectedResult(n, r)
{
  var k := if r < n - 1 then r else n - 1;
  result := k * (k + 1) / 2 + (if r >= n then 1 else 0);
}
// </vc-code>

