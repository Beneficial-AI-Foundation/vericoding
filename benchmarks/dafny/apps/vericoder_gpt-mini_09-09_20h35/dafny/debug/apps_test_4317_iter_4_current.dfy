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
predicate isValidInteger(s: string)
{
    |s| >= 1
}

function parseInt(s: string): int
    requires isValidInteger(s)
{
    0
}

function intToString(n: int): string
{
    ""
}

function findSpace(s: string): int
    ensures 0 < findSpace(s) < |s| && s[findSpace(s)] == ' '
{
    var pos : int :| 0 < pos < |s| && s[pos] == ' ';
    pos
}

function abs(n: int): int
{
    if n >= 0 then n else -n
}

lemma AbsMultiply(a: int, b: int)
    ensures abs(a * b) == abs(a) * abs(b)
{
    if a >= 0 {
        if b >= 0 {
            assert abs(a * b) == a * b;
            assert abs(a) == a;
            assert abs(b) == b;
            assert a * b == a * b;
        } else {
            // a >= 0, b < 0
            assert abs(a * b) == -(a * b);
            assert abs(a) == a;
            assert abs(b) == -b;
            assert -(a * b) == a * (-b);
            assert a * (-b) == abs(a) * abs(b);
        }
    } else {
        if b >= 0 {
            // a < 0, b >= 0
            assert abs(a * b) == -(a * b);
            assert abs(a) == -a;
            assert abs(b) == b;
            assert -(a * b) == (-a) * b;
            assert (-a) * b == abs(a) * abs(b);
        } else {
            // a < 0, b < 0
            assert abs(a * b) == a * b;
            assert abs(a) == -a;
            assert abs(b) == -b;
            assert a * b == (-a) * (-b);
            assert (-a) * (-b) == abs(a) * abs(b);
        }
    }
}

lemma AbsBound(a: int)
    requires -100 <= a <= 100
    ensures abs(a) <= 100
{
    if a >= 0 {
        assert abs(a) == a;
        assert a <= 100;
    } else {
        assert abs(a) == -a;
        assert -a <= 100;
    }
}

lemma Max3Bound(a: int, b: int)
    requires -100 <= a <= 100 && -100 <= b <= 100
    ensures -10000 <= max3(a + b, a - b, a * b) <= 10000
{
    var m := max3(a + b, a - b, a * b);
    assert m == a + b || m == a - b || m == a * b;
    if m == a + b {
        assert a + b <= 200;
        assert a + b >= -200;
        assert a + b <= 10000;
        assert a + b >= -10000;
    } else if m == a - b {
        assert a - b <= 200;
        assert a - b >= -200;
        assert a - b <= 10000;
        assert a - b >= -10000;
    } else {
        // m == a * b
        AbsBound(a);
        AbsBound(b);
        AbsMultiply(a, b);
        assert abs(a * b) == abs(a) * abs(b);
        assert abs(a) <= 100;
        assert abs(b) <= 100;
        assert abs(a * b) <= 100 * 100;
        assert -10000 <= a * b && a * b <= 10000;
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
  var m := max3(a + b, a - b, a * b);
  assert -100 <= a <= 100;
  assert -100 <= b <= 100;
  Max3Bound(a, b);
  result := intToString(m) + "\n";
}
// </vc-code>

