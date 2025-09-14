predicate ValidInput(input: string)
{
    |input| >= 3 &&
    exists spacePos :: 0 < spacePos < |input| - 1 && input[spacePos] == ' ' &&
    (forall i :: 0 <= i < spacePos ==> input[i] != ' ') &&
    (forall i :: spacePos + 1 <= i < |input| ==> input[i] != ' ' || input[i] == '\n') &&
    isValidInteger(getAString(input)) && isValidInteger(getBString(input)) &&
    -100 <= getA(input) <= 100 && -100 <= getB(input) <= 100
}

function getA(input: string): int
    requires |input| >= 3
    requires exists spacePos :: 0 < spacePos < |input| - 1 && input[spacePos] == ' '
    requires isValidInteger(getAString(input))
{
    var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
    var spaceIndex := findSpace(trimmed);
    parseInt(trimmed[..spaceIndex])
}

function getB(input: string): int
    requires |input| >= 3
    requires exists spacePos :: 0 < spacePos < |input| - 1 && input[spacePos] == ' '
    requires isValidInteger(getBString(input))
{
    var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
    var spaceIndex := findSpace(trimmed);
    parseInt(trimmed[spaceIndex+1..])
}

function getAString(input: string): string
    requires |input| >= 3
    requires exists spacePos :: 0 < spacePos < |input| - 1 && input[spacePos] == ' '
{
    var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
    var spaceIndex := findSpace(trimmed);
    trimmed[..spaceIndex]
}

function getBString(input: string): string
    requires |input| >= 3
    requires exists spacePos :: 0 < spacePos < |input| - 1 && input[spacePos] == ' '
{
    var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
    var spaceIndex := findSpace(trimmed);
    trimmed[spaceIndex+1..]
}

function max3(a: int, b: int, c: int): int
    ensures max3(a, b, c) >= a && max3(a, b, c) >= b && max3(a, b, c) >= c
    ensures max3(a, b, c) == a || max3(a, b, c) == b || max3(a, b, c) == c
{
    if a >= b && a >= c then a
    else if b >= c then b
    else c
}

// <vc-helpers>
lemma Max3InsideBounds(x:int, y:int, z:int, L:int, U:int)
  requires L <= x <= U
  requires L <= y <= U
  requires L <= z <= U
  ensures L <= max3(x, y, z) <= U
{
  assert max3(x, y, z) >= x && max3(x, y, z) >= y && max3(x, y, z) >= z;
  assert max3(x, y, z) == x || max3(x, y, z) == y || max3(x, y, z) == z;
  assert L <= max3(x, y, z);
  if max3(x, y, z) == x {
    assert max3(x, y, z) <= U;
  } else if max3(x, y, z) == y {
    assert max3(x, y, z) <= U;
  } else {
    assert max3(x, y, z) == z;
    assert max3(x, y, z) <= U;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures var maxVal := max3(getA(input) + getB(input), getA(input) - getB(input), getA(input) * getB(input));
            result == intToString(maxVal) + "\n"
    ensures var maxVal := max3(getA(input) + getB(input), getA(input) - getB(input), getA(input) * getB(input));
            -10000 <= maxVal <= 10000
// </vc-spec>
// <vc-code>
{
  var a := getA(input);
  var b := getB(input);
  assert -100 <= a <= 100;
  assert -100 <= b <= 100;

  var x := a + b;
  var y := a - b;
  var z := a * b;

  assert -200 <= x <= 200;
  assert -200 <= y <= 200;
  assert -10000 <= z <= 10000;

  assert -10000 <= x;
  assert x <= 10000;
  assert -10000 <= y;
  assert y <= 10000;

  Max3InsideBounds(x, y, z, -10000, 10000);

  result := intToString(max3(x, y, z)) + "\n";
}
// </vc-code>

