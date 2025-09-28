predicate ValidInput(r: int, g: int, b: int) {
    r >= 0 && g >= 0 && b >= 0
}

function MaxTables(r: int, g: int, b: int): int
    requires ValidInput(r, g, b)
{
    min(min(min((r + g + b) / 3, r + g), r + b), g + b)
}

function min(a: int, b: int): int {
    if a <= b then a else b
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(r: int, g: int, b: int) returns (result: int)
    requires ValidInput(r, g, b)
    ensures result == MaxTables(r, g, b)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
  var sum := r + g + b;
  var avg := sum / 3;
  var rg := r + g;
  var rb := r + b;
  var gb := g + b;
  var m1 := if avg <= rg then avg else rg;
  var m2 := if rb <= gb then rb else gb;
  result := if m1 <= m2 then m1 else m2;
}
// </vc-code>

