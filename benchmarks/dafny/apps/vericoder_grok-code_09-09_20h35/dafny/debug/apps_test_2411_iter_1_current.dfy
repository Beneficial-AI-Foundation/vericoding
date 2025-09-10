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

predicate isNonNegativeNumericString(s: string)
{
  |s| > 0 && s[0] != '-' && (forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9')
}

predicate isNumericString(s: string)
{
  |s| > 0 && (s[0] == '-' || (forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'))
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

predicate isNonNegativeNumericString(s: string)
{
  |s| > 0 && s[0] != '-' && (forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9')
}

predicate isNumericString(s: string)
{
  |s| > 0 && (s[0] == '-' || (forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'))
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
// </vc-code>

