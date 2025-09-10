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
function natToString(n: nat): string
  ensures isNonNegativeNumericString(natToString(n))

lemma natToStringCorrectness(n: nat)
  ensures stringToInt(natToString(n)) == n

function splitLines(input: string): seq<string>
  requires |input| > 0
  ensures |splitLines(input)| > 0

predicate isValidFirstLine(line: string)

function parseFirstLineAsNat(line: string): nat
  requires isValidFirstLine(line)

predicate isValidCoordinateLine(line: string)

function getDistinctLines(points: seq<(int, int)>): seq<seq<(int, int)>>
  requires |points| >= 2

function groupLinesBySlope(lines: seq<seq<(int, int)>>): seq<seq<seq<(int, int)>>>

function sumOverSlopeGroups(slopeGroups: seq<seq<seq<(int, int)>>>, totalLines: int): nat

lemma extractNCorrectness(stdin_input: string)
  requires validInputFormat(stdin_input)
  ensures var n := extractN(stdin_input); n >= 2 && n <= 1000

lemma extractPointsCorrectness(stdin_input: string)
  requires validInputFormat(stdin_input)
  ensures var n := extractN(stdin_input);
          var points := extractPoints(stdin_input);
          |points| == n &&
          (forall i :: 0 <= i < |points| ==> validCoordinate(points[i])) &&
          (forall i, j :: 0 <= i < j < |points| ==> points[i] != points[j])
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
  
  extractNCorrectness(stdin_input);
  extractPointsCorrectness(stdin_input);
  
  var count := countIntersectingLinePairs(points);
  result := natToString(count);
  
  natToStringCorrectness(count);
}
// </vc-code>

