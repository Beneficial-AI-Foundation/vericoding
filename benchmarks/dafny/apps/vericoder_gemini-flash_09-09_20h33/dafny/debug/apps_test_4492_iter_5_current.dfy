predicate ValidInput(input: string)
{
    var lines := SplitByNewlineSpec(input);
    |lines| >= 2 &&
    var firstLine := SplitBySpaceSpec(lines[0]);
    |firstLine| >= 2 &&
    var N := ParseIntSpec(firstLine[0]);
    var x := ParseIntSpec(firstLine[1]);
    N >= 2 && x >= 0 &&
    var secondLine := SplitBySpaceSpec(lines[1]);
    |secondLine| == N &&
    (forall i :: 0 <= i < N ==> ParseIntSpec(secondLine[i]) >= 0)
}

function MinimumCandiesNeeded(input: string): int
    requires ValidInput(input)
    ensures MinimumCandiesNeeded(input) >= 0
{
    var lines := SplitByNewlineSpec(input);
    var firstLine := SplitBySpaceSpec(lines[0]);
    var N := ParseIntSpec(firstLine[0]);
    var x := ParseIntSpec(firstLine[1]);
    var secondLine := SplitBySpaceSpec(lines[1]);
    var A := seq(N, i requires 0 <= i < N => ParseIntSpec(secondLine[i]));
    ComputeMinimumOperations(A, x)
}

function ComputeMinimumOperations(A: seq<int>, x: int): int
    requires |A| >= 2
    requires x >= 0
    requires forall i :: 0 <= i < |A| ==> A[i] >= 0
    ensures ComputeMinimumOperations(A, x) >= 0
{
    var A0 := if A[0] > x then x else A[0];
    var cnt0 := if A[0] > x then A[0] - x else 0;
    ComputeOperationsFromIndex(A, x, 1, [A0] + A[1..], cnt0)
}

function ComputeOperationsFromIndex(originalA: seq<int>, x: int, index: int, currentA: seq<int>, currentCount: int): int
    requires |originalA| >= 2
    requires x >= 0
    requires 1 <= index <= |originalA|
    requires |currentA| == |originalA|
    requires currentCount >= 0
    requires forall i :: 0 <= i < |originalA| ==> originalA[i] >= 0
    ensures ComputeOperationsFromIndex(originalA, x, index, currentA, currentCount) >= currentCount
    decreases |originalA| - index
{
    if index >= |originalA| then currentCount
    else
        var newValue := if currentA[index] + currentA[index-1] > x then x - currentA[index-1] else currentA[index];
        var additionalOps := if currentA[index] + currentA[index-1] > x then currentA[index] + currentA[index-1] - x else 0;
        var newA := currentA[index := newValue];
        ComputeOperationsFromIndex(originalA, x, index + 1, newA, currentCount + additionalOps)
}

// <vc-helpers>
function ParseIntSpec(s: string): int
  reads s
{
  var n := 0;
  var sign := 1;
  var i := 0;

  if i < |s| && (s[i] == '-' || s[i] == '+') then
  (
    if s[i] == '-' then sign := -1
    else sign := 1;
    i := i + 1;
  )
  else if i < |s| && ('0' <= s[i] <= '9') then
  (
    // If no sign, 'sign' remains 1, 'i' remains 0.
    // This 'else if' block handles the case where there is no sign but a digit.
  )
  else
  (
    // Handle cases where s is empty, or starts with non-digit/non-sign characters.
    // In such cases, 0 is returned, which is fine for current usage.
    return 0;
  )

  while i < |s|
    invariant 0 <= i <= |s|
    invariant n >= 0
    invariant (forall k :: (if (s[0] == '-' || s[0] == '+') then 1 else 0) <= k < i ==> '0' <= s[k] <= '9')
  {
    var digit := s[i] as int - '0' as int;
    n := n * 10 + digit;
    i := i + 1;
  }
  return sign * n;
}

function SplitBySpaceSpec(s: string): seq<string>
  reads s
{
  var result: seq<string> := [];
  var currentWord: string := "";
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant forall k :: 0 <= k < i ==> s[k] != '\n'
    invariant forall j :: 0 <= j < |result| ==> |result[j]| > 0
    invariant result == GetWordsBeforeIndex(s, i)
    invariant currentWord == GetTrailingWord(s, i)
  {
    if i < |s| && s[i] != ' ' then
      currentWord := currentWord + s[i];
    else
      if |currentWord| > 0 then
        result := result + [currentWord];
      currentWord := "";
  }
  if |currentWord| > 0 then
    result := result + [currentWord];
  return result;
}

// Helper function for SplitBySpaceSpec to satisfy invariants
function GetWordsBeforeIndex(s: string, index: int): seq<string>
  requires 0 <= index <= |s|
{
  var res: seq<string> := [];
  var current: string := "";
  for i := 0 to index - 1
  {
    if s[i] != ' ' then
      current := current + s[i];
    else
      if |current| > 0 then
        res := res + [current];
      current := "";
  }
  return res;
}

// Helper function for SplitBySpaceSpec to satisfy invariants
function GetTrailingWord(s: string, index: int): string
  requires 0 <= index <= |s|
{
    var currentWord: string := "";
    if index > 0 && s[index-1] != ' ' {
        var k := index - 1;
        while k >= 0 && s[k] != ' ' {
            k := k - 1;
        }
        currentWord := s[k+1..index];
    }
    return currentWord;
}

function SplitByNewlineSpec(s: string): seq<string>
  reads s
{
  var result: seq<string> := [];
  var currentLine: string := "";
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant forall j :: 0 <= j < |result| ==> '\n' !in result[j] && |result[j]| > 0
    invariant result == GetLinesBeforeIndex(s, i)
    invariant currentLine == GetTrailingLine(s, i)
  {
    if i < |s| && s[i] != '\n' then
      currentLine := currentLine + s[i];
    else
      if |currentLine| > 0 then
        result := result + [currentLine];
      currentLine := "";
  }
  if |currentLine| > 0 then
    result := result + [currentLine];
  return result;
}

// Helper function for SplitByNewlineSpec to satisfy invariants
function GetLinesBeforeIndex(s: string, index: int): seq<string>
  requires 0 <= index <= |s|
{
  var res: seq<string> := [];
  var current: string := "";
  for i := 0 to index - 1
  {
    if s[i] != '\n' then
      current := current + s[i];
    else
      if |current| > 0 then
        res := res + [current];
      current := "";
  }
  return res;
}

// Helper function for SplitByNewlineSpec to satisfy invariants
function GetTrailingLine(s: string, index: int): string
  requires 0 <= index <= |s|
{
    var currentLine: string := "";
    if index > 0 && s[index-1] != '\n' {
        var k := index - 1;
        while k >= 0 && s[k] != '\n' {
            k := k - 1;
        }
        currentLine := s[k+1..index];
    }
    return currentLine;
}

function IntToString(n: int): string
  requires n >= 0   // Simplified for non-negative integers as per problem context
  ensures |IntToString(n)| >= 1
  ensures (n == 0) ==> (IntToString(n) == "0")
  ensures (n > 0) ==> (IntToString(n) != "0")
{
  if n == 0 then "0"
  else
    var s := "";
    var temp := n;
    while temp > 0
      invariant temp >= 0
      invariant (temp > 0 ==> temp / 10 < temp)
      invariant forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9'
      invariant n == (temp * (10 as int ^ |s| as nat)) + StringToInt(s)
    {
      s := ((temp % 10) as char + '0') + s;
      temp := temp / 10;
    }
    s
}

// Helper function to convert string to int for invariant in IntToString
function StringToInt(s: string): int
  requires forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9'
  reads s
{
  var n := 0;
  for i := 0 to |s| - 1
  {
    n := n * 10 + (s[i] as int - '0' as int);
  }
  return n;
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    requires ValidInput(input)
    ensures |result| > 0
    ensures result == IntToString(MinimumCandiesNeeded(input)) + "\n"
// </vc-spec>
// <vc-code>
{
  var resultValue := MinimumCandiesNeeded(input);
  result := IntToString(resultValue) + "\n";
}
// </vc-code>

