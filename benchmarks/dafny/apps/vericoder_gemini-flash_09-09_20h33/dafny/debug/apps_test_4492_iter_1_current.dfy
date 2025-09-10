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
    if s[i] == '-' then sign := -1;
    i := i + 1;

  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall k :: 0 <= k < i && '0' <= s[k] <= '9' ==> true
    invariant n >= 0
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

function SplitByNewlineSpec(s: string): seq<string>
  reads s
{
  var result: seq<string> := [];
  var currentLine: string := "";
  for i := 0 to |s|
    invariant 0 <= i <= |s|
  {
    if i < |s| && s[i] != '\n' then
      currentLine := currentLine + s[i];
    else
      result := result + [currentLine];
      currentLine := "";
  }
  return result;
}

function IntToString(n: int): string
  requires n >= 0   // Simplified for non-negative integers as per problem context
  ensures |IntToString(n)| >= 1
{
  if n == 0 then "0"
  else
    var s := "";
    var temp := n;
    while temp > 0
      invariant temp >= 0
    {
      s := (temp % 10 as char) + s;
      temp := temp / 10;
    }
    s
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

