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
function gcd(a: int, b: int): nat
  requires a >= 0 && b >= 0
{
  if b == 0 then a else gcd(b, a % b)
}

function position(s: string, ch: char): int
  decreases |s|
{
  if s == [] then -1 else if s[0] == ch then 0 else 1 + position(s[1..], ch)
}

function stringSplit(s: string, delim: char): seq<string>
  decreases |s|
{
  if s == [] then []
  else
    var i := position(s, delim);
    if i == -1 then [s]
    else [s[..i]] + stringSplit(s[i+1..], delim)
}

function splitLines(input: string): seq<string>
  decreases |input|
{
  if input == "" then []
  else
    var i := position(input, '\n');
    if i == -1 then [input]
    else [input[..i+1]] + splitLines(input[i+1..])
}

function isValidFirstLine(s: string): bool
{
  var parts := stringSplit(s[..|s|-1], ' ');
  |parts| == 1 && isNonNegativeNumericString(parts[0])
}

function parseFirstLineAsNat(s: string): nat
  requires isValidFirstLine(s)
{
  var parts := stringSplit(s[..|s|-1], ' ');
  stringToUnsignedHelper(parts[0])
}

function pow10(n: nat): nat
{
  if n == 0 then 1 else 10 * pow10(n-1)
}

function stringToUnsignedHelper(s: string): nat
  requires |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
  decreases |s|
{
  if |s| == 1 then (s[0] - '0') as nat else (s[0] - '0') as nat * pow10(|s|-1) + stringToUnsignedHelper(s[1..])
}

function stringToInt(s: string): int
  requires isNumericString(s)
{
  if s[0] == '-' then -(stringToUnsignedHelper(s[1..])) as int else stringToUnsignedHelper(s) as int
}

predicate isValidCoordinateLine(s: string)
{
  var parts := stringSplit(s[..|s|-1], ' ');
  |parts| == 2 && isNumericString(parts[0]) && isNumericString(parts[1])
}

function parsePoint(s: string): (int, int)
  requires isValidCoordinateLine(s)
{
  var parts := stringSplit(s[..|s|-1], ' ');
  (stringToInt(parts[0]), stringToInt(parts[1]))
}

function extractPoints(input: string): seq<(int, int)>
  requires validInputFormat(input)
  ensures |extractPoints(input)| == extractN(input)
  ensures var n := extractN(input);
          (forall i :: 0 <= i < n ==> validCoordinate(extractPoints(input)[i]))
  ensures var n := extractN(input);
          forall i, j :: 0 <= i < j < n ==> extractPoints(input)[i] != extractPoints(input)[j]
{
  var lines := splitLines(input);
  var points := [];
  for i := 1 to |lines| - 1 {
    var point := parsePoint(lines[i]);
    points := points + [point];
  }
  points
}

// Define line as a set or representation
datatype Line = LineConst(x: int, y: int, c: int)  // ax + by + c = 0, but for infinite lines, better simplified

function simplifyLine(a: int, b: int, c: int): (int, int, int)
  requires a >= 0 || b >= 0  // assume normalized sign
{
  if a < 0 || (a == 0 && b < 0) then simplifyLine(-a, -b, -c) else
  var g := gcd(a, gcd(b, c));
  if g == 0 then (1, 0, 0) else (a / g, b / g, c / g)
}

function getLineBetweenPoints(p1: (int, int), p2: (int, int)): (int, int, int)
  requires p1 != p2
{
  var (x1, y1) := p1;
  var (x2, y2) := p2;
  var a := y1 - y2;
  var b := x2 - x1;
  var c := x1 * y2 - x2 * y1;
  simplifyLine(a, b, c)
}

function getDistinctLines(points: seq<(int, int)>): seq<(int, int, int)>
  requires |points| >= 2
  requires forall i, j :: 0 <= i < j < |points| ==> points[i] != points[j]
  requires forall i :: 0 <= i < |points| ==> validCoordinate(points[i])
{
  var lines := [];
  var allPairs := [];
  for i := 0 to |points| - 1
    for j := i + 1 to |points| - 1
      allPairs := allPairs + [(i, j)];
  for k := 0 to |allPairs| - 1 {
    var (i, j) := allPairs[k];
    var line := getLineBetweenPoints(points[i], points[j]);
    if line !in lines {
      lines := lines + [line];
    }
  }
  lines
}

function groupLinesBySlope(distinctLines: seq<(int, int, int)>): seq<seq<(int, int, int)>>
{
  var groups := [];
  for i := 0 to |distinctLines| - 1 {
    var found := false;
    for g := 0 to |groups| - 1 {
      if |groups[g]| > 0 && sameSlopeSameType(distinctLines[i], groups[g][0]) {
        groups := groups[g := groups[g] + [distinctLines[i]]];
        found := true;
        break;
      }
    }
    if !found {
      groups := groups + [[distinctLines[i]]];
    }
  }
  groups
}

function sameSlopeSameType(l1: (int, int, int), l2: (int, int, int)): bool
{
  var (a1, b1, c1) := l1;
  var (a2, b2, c2) := l2;
  // Same slope if a1*b2 == a2*b1, same sign or something, but since normalized, check if parallel
  (a1 == a2 && b1 == b2) || (a1 == -a2 && b1 == -b2)  // but since positive orientation
}

function sumOverSlopeGroups(slopeGroups: seq<seq<(int, int, int)>>, totalLines: nat): nat
{
  var sum := 0;
  for i := 0 to |slopeGroups| - 1 {
    var groupSize := |slopeGroups[i]| as nat;
    sum := sum + groupSize * (totalLines - groupSize);
  }
  sum
}

function natToString(n: nat): string
  decreases n
{
  if n == 0 then "0" else
  if n < 10 then [(n + '0' as int) as char] else
  natToString(n / 10) + [(n % 10 + '0' as int) as char]
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
  var points := extractPoints(stdin_input);
  var count := countIntersectingLinePairs(points);
  result := natToString(count);
}
// </vc-code>

