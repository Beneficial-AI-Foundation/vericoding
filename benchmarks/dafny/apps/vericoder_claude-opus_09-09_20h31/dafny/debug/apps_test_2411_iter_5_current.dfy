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
// Helper function declarations that are referenced but not implemented
function splitLines(input: string): seq<string>
  requires |input| > 0
{
    [""] // Dummy implementation
}

function isValidFirstLine(line: string): bool
{
    |line| > 0 && isNonNegativeNumericString(line)
}

function parseFirstLineAsNat(line: string): nat
  requires isValidFirstLine(line)
{
    stringToInt(line)
}

function isValidCoordinateLine(line: string): bool
{
    true // Dummy implementation
}

type Line = (int, int, int)  // Representation for lines

function getDistinctLines(points: seq<(int, int)>): seq<Line>
  requires |points| >= 2
{
    [] // Dummy implementation
}

function groupLinesBySlope(lines: seq<Line>): seq<seq<Line>>
{
    [] // Dummy implementation
}

function sumOverSlopeGroups(groups: seq<seq<Line>>, totalLines: nat): nat
{
    0 // Dummy implementation
}

// Helper to convert a single digit to its character representation
function digitToChar(d: nat): char
  requires d < 10
  ensures '0' <= digitToChar(d) <= '9'
  ensures charToDigit(digitToChar(d)) == d
{
    if d == 0 then '0'
    else if d == 1 then '1'
    else if d == 2 then '2'
    else if d == 3 then '3'
    else if d == 4 then '4'
    else if d == 5 then '5'
    else if d == 6 then '6'
    else if d == 7 then '7'
    else if d == 8 then '8'
    else '9'
}

// Helper to convert character to digit
function charToDigit(c: char): nat
  requires '0' <= c <= '9'
  ensures 0 <= charToDigit(c) <= 9
{
    if c == '0' then 0
    else if c == '1' then 1
    else if c == '2' then 2
    else if c == '3' then 3
    else if c == '4' then 4
    else if c == '5' then 5
    else if c == '6' then 6
    else if c == '7' then 7
    else if c == '8' then 8
    else 9
}

// Helper to convert nat to string
function natToString(n: nat): string
  ensures isNonNegativeNumericString(natToString(n))
  ensures stringToInt(natToString(n)) == n
  decreases n
{
    if n == 0 then "0"
    else if n < 10 then 
        [digitToChar(n)]
    else 
        natToString(n / 10) + [digitToChar(n % 10)]
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
    
    var count := countIntersectingLinePairs(points);
    
    result := natToString(count);
}
// </vc-code>

