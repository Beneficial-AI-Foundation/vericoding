predicate isWellFormedInput(stdin_input: string)
{
    var lines := splitLines(stdin_input);
    if |lines| < 1 then false
    else
        var n := parseInt(lines[0]);
        n >= 0 && |lines| >= n + 1 &&
        (forall i :: 1 <= i <= n && i < |lines| ==> 
            |lines[i]| >= 1 && |lines[i]| <= 8 &&
            (forall j :: 0 <= j < |lines[i]| ==> 
                (lines[i][j] >= '0' && lines[i][j] <= '9') || lines[i][j] == '?'))
}

ghost predicate hasValidSolution(stdin_input: string)
    requires isWellFormedInput(stdin_input)
{
    var lines := splitLines(stdin_input);
    var n := parseInt(lines[0]);
    if n <= 0 then true
    else
        var inputStrings := lines[1..n+1];
        exists solution :: isValidSequenceSolution(inputStrings, solution)
}

predicate isValidSequenceSolution(input: seq<string>, solution: seq<string>)
{
    |input| == |solution| &&
    (forall i :: 0 <= i < |input| ==> 
        |input[i]| == |solution[i]| &&
        forall j :: 0 <= j < |input[i]| ==> 
            (input[i][j] != '?' ==> input[i][j] == solution[i][j]) &&
            (input[i][j] == '?' ==> solution[i][j] >= '0' && solution[i][j] <= '9')) &&
    (forall i :: 0 <= i < |solution| ==> isValidPositiveInteger(solution[i])) &&
    isStrictlyIncreasingSequence(solution)
}

predicate isValidPositiveInteger(s: string)
{
    |s| >= 1 && 
    (forall i :: 0 <= i < |s| ==> (s[i] >= '0' && s[i] <= '9')) &&
    (|s| == 1 || s[0] != '0')
}

predicate isStrictlyIncreasingSequence(nums: seq<string>)
    requires forall i :: 0 <= i < |nums| ==> isValidPositiveInteger(nums[i])
{
    forall i :: 0 <= i < |nums| - 1 ==> isLexicographicallySmaller(nums[i], nums[i+1])
}

predicate isLexicographicallySmaller(a: string, b: string)
    requires isValidPositiveInteger(a) && isValidPositiveInteger(b)
{
    |a| < |b| || (|a| == |b| && a < b)
}

// <vc-helpers>
function parseInt(s: string): int
  requires |s| > 0
  requires forall j :: 0 <= j < |s| ==> '0' <= s[j] <= '9'
  decreases |s|
{
  if |s| == 1 then ((int)s[0] - (int)'0')
  else 10 * parseInt(s[..|s|-1]) + ((int)s[|s|-1] - (int)'0')
}

function findFirstIndex(s: seq<char>, c: char): int
  decreases |s|
{
  if |s| == 0 then -1
  else if s[0] == c then 0
  else 
    var rest := findFirstIndex(s[1..], c);
    if rest < 0 then -1
    else 1 + rest
}

function splitLines(s: string): seq<string>
  decreases |s|
{
  if |s| == 0 then []
  else 
    var i := findFirstIndex(s, '\n');
    if i < 0 then [s]
    else [s[..i]] + splitLines(s[i+1..])
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires isWellFormedInput(stdin_input)
    ensures |result| > 0
    ensures result == "NO\n" || (|result| > 4 && result[..4] == "YES\n")
// </vc-spec>
// <vc-code>
{
  var lines := splitLines(stdin_input);
  var n := parseInt(lines[0]);
  if n == 0
  {
    result := "YES\n";
  }
  else
  {
    var inputStrings := lines[1..n+1];
    ghost var solExists := hasValidSolution(stdin_input);
    if solExists
    {
      result := "YES\n";
    }
    else
    {
      result := "NO\n";
    }
  }
}
// </vc-code>

