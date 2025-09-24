// <vc-preamble>
predicate ValidInput(d1: int, d2: int, d3: int) {
  d1 >= 1 && d2 >= 1 && d3 >= 1 &&
  d1 <= 100000000 && d2 <= 100000000 && d3 <= 100000000
}

function Route1Distance(d1: int, d2: int, d3: int): int {
  2 * d1 + 2 * d2
}

function Route2Distance(d1: int, d2: int, d3: int): int {
  d1 + d3 + d2
}

function Route3Distance(d1: int, d2: int, d3: int): int {
  2 * d1 + 2 * d3
}

function Route4Distance(d1: int, d2: int, d3: int): int {
  2 * d2 + 2 * d3
}

function MinimumDistance(d1: int, d2: int, d3: int): int {
  var r1 := Route1Distance(d1, d2, d3);
  var r2 := Route2Distance(d1, d2, d3);
  var r3 := Route3Distance(d1, d2, d3);
  var r4 := Route4Distance(d1, d2, d3);
  
  if r1 <= r2 && r1 <= r3 && r1 <= r4 then r1
  else if r2 <= r3 && r2 <= r4 then r2
  else if r3 <= r4 then r3
  else r4
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(d1: int, d2: int, d3: int) returns (result: int)
  requires ValidInput(d1, d2, d3)
  ensures result == MinimumDistance(d1, d2, d3)
  ensures result <= Route1Distance(d1, d2, d3)
  ensures result <= Route2Distance(d1, d2, d3)
  ensures result <= Route3Distance(d1, d2, d3)
  ensures result <= Route4Distance(d1, d2, d3)
// </vc-spec>
// <vc-code>
{
  var D1 := 2 * d1 + 2 * d2;
  var D2 := d1 + d3 + d2;
  var D3 := (d1 + d3) * 2;
  var D4 := (d2 + d3) * 2;

  result := D1;
  if D2 < result {
    result := D2;
  }
  if D3 < result {
    result := D3;
  }
  if D4 < result {
    result := D4;
  }
}
// </vc-code>
