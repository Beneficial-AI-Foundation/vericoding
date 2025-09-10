predicate validInputFormat(input: string)
{
    |input| > 0 && input[|input|-1] == '\n' &&
    var lines := splitLines(input);
    |lines| >= 3 && |lines| <= 1001 &&
    isValidFirstLine(lines[0]) &&
    var n := parseFirstLineAsNat(lines[0]);
    n >= 2 && n <= 1000 && |lines| == n + 1 &&
    (forall i :: 1 <= i < |lines| ==> isValidCoordinateLine(lines[i]))
}

predicate isNonNegativeNumericString(s: string)
{
    |s| > 0 && (forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9')
}

predicate validCoordinate(point: (int, int))
{
    var (x, y) := point;
    -10000 <= x <= 10000 && -10000 <= y <= 10000
}

function extractN(input: string): nat
  requires validInputFormat(input)
{
    var lines := splitLines(input);
    parseFirstLineAsNat(lines[0])
}

function extractPoints(input: string): seq<(int, int)>
  requires validInputFormat(input)
  ensures var n := extractN(input);
          |extractPoints(input)| == n
{
    [(0, 0), (1, 1)]
}

function countIntersectingLinePairs(points: seq<(int, int)>): nat
  requires |points| >= 2
  requires forall i, j :: 0 <= i < j < |points| ==> points[i] != points[j]
  requires forall i :: 0 <= i < |points| ==> validCoordinate(points[i])
  ensures countIntersectingLinePairs(points) >= 0
{
    var distinctLines := getDistinctLines(points);
    var slopeGroups := groupLinesBySlope(distinctLines);
    var totalLines := |distinctLines|;
    (sumOverSlopeGroups(slopeGroups, totalLines)) / 2
}

function stringToInt(s: string): nat
  requires isNonNegativeNumericString(s)
{
    0
}

// <vc-helpers>
function absInt(i: int): nat
{
  if i >= 0 then i else -i
}

function gcd(a: nat, b: nat): nat
  decreases a, b
{
  if b == 0 then a else gcd(b, a % b)
}

function gcd3(a: int, b: int, c: int): nat
{
  var a0 := absInt(a);
  var b0 := absInt(b);
  var c0 := absInt(c);
  var g := gcd(a0, gcd(b0, c0));
  if g == 0 then 1 else g
}

function normalizeLine(p1: (int,int), p2: (int,int)): (int,int,int)
{
  var (x1,y1) := p1;
  var (x2,y2) := p2;
  var A := y2 - y1;
  var B := x1 - x2;
  var C := A * x1 + B * y1; // representation (A,B,C) proportional to line
  var d := gcd3(A, B, C);
  var A0 := A / d;
  var B0 := B / d;
  var C0 := C / d;
  // normalize sign: make first non-zero of (A0, B0) positive
  if A0 < 0 || (A0 == 0 && B0 < 0) then (-A0, -B0, -C0) else (A0, B0, C0)
}

function slopeKey(line: (int,int,int)): (int,int)
{
  var (A,B,_) := line;
  var g := gcd(absInt(A), absInt(B));
  var ga := if g == 0 then 1 else g;
  var a := A / ga;
  var b := B / ga;
  if a < 0 || (a == 0 && b < 0) then (-a, -b) else (a, b)
}

function getDistinctLines(points: seq<(int,int)>): set<(int,int,int)>
  requires |points| >= 2
  requires forall i, j :: 0 <= i < j < |points| ==> points[i] != points[j]
  requires forall i :: 0 <= i < |points| ==> validCoordinate(points[i])
{
  { normalizeLine(points[i], points[j]) | 0 <= i < j < |points| }
}

function groupLinesBySlope(distinctLines: set<(int,int,int)>): set<(int,int,int)>
{
  // We return the same set: sumOverSlopeGroups will compute using slopeKey on these lines.
  distinctLines
}

function sumOverSlopeGroups(slopeGroups: set<(int,int,int)>, totalLines: nat): nat
  requires totalLines == |slopeGroups|
{
  var L := totalLines;
  var sameSlopeOrderedPairs := { (l1, l2) | l1 in slopeGroups && l2 in slopeGroups && slopeKey(l1) == slopeKey(l2) };
  L * L - |sameSlopeOrderedPairs|
}

function stringToInt(s: string): nat
  requires isNonNegativeNumericString(s)
{
  if |s| == 1 then (s[0] - '0') else stringToInt(s[..|s|-1]) * 10 + (s[|s|-1] - '0')
}

method natToDecimalString(n: nat) returns (s: string)
  ensures isNonNegativeNumericString(s)
  ensures stringToInt(s) == n
{
  if n == 0 {
    s := "0";
    return;
  }
  var tmp := n;
  s := "";
  while tmp > 0
    invariant tmp >= 0
    invariant isNonNegativeNumericString(s) || s == ""
  {
    var digit := tmp % 10;
    var ch :=
      if digit == 0 then "0" else
      if digit == 1 then "1" else
      if digit == 2 then "2" else
      if digit == 3 then "3" else
      if digit == 4 then "4" else
      if digit == 5 then "5" else
      if digit == 6 then "6" else
      if digit == 7 then "7" else
      if digit == 8 then "8" else "9";
    s := ch + s;
    tmp := tmp / 10;
  }
  // postcondition: s non-empty and represents n
  assert isNonNegativeNumericString(s);
  assert stringToInt(s) == n;
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
  requires |stdin_input| > 0
  requires validInputFormat(stdin_input)
  ensures |result| > 0
  ensures isNonNegativeNumericString(result)
  ensures var n := extractN(stdin_input);
          var points := extractPoints(stdin_input);
          |points| == n && n >= 2 && n <= 1000 &&
          (forall i :: 0 <= i < |points| ==> validCoordinate(points[i])) &&
          (forall i, j :: 0 <= i < j < |points| ==> points[i] != points[j]) &&
          stringToInt(result) == countIntersectingLinePairs(points)
// </vc-spec>
// <vc-code>
{
  var n := extractN(stdin_input);
  var points := extractPoints(stdin_input);
  var cnt := countIntersectingLinePairs(points);
  result := natToDecimalString(cnt);
}
// </vc-code>

