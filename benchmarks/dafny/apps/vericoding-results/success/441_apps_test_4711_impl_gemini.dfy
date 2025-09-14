predicate ValidInput(a: int, b: int, c: int) {
    1 <= a <= 10000 && 1 <= b <= 10000 && 1 <= c <= 10000
}

function MinOfThree(x: int, y: int, z: int): int {
    if x <= y && x <= z then x
    else if y <= z then y
    else z
}

function CorrectResult(a: int, b: int, c: int): int {
    MinOfThree(a + b, a + c, b + c)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int, c: int) returns (result: int)
    requires ValidInput(a, b, c)
    ensures result == CorrectResult(a, b, c)
// </vc-spec>
// <vc-code>
{
  var sum_ab := a + b;
  var sum_ac := a + c;
  var sum_bc := b + c;
  if sum_ab <= sum_ac && sum_ab <= sum_bc {
    result := sum_ab;
  } else if sum_ac <= sum_bc {
    result := sum_ac;
  } else {
    result := sum_bc;
  }
}
// </vc-code>

