predicate ValidInputFormat(input: string)
{
    |input| > 0 && 
    exists lines: seq<string> ::
        lines == SplitLines(input) &&
        |lines| >= 1 &&
        IsValidInteger(lines[0]) &&
        var t := StringToInt(lines[0]);
        1 <= t <= 100 &&
        |lines| >= 1 + 3*t &&
        forall i :: 0 <= i < t ==> 
            var base_idx := 1 + 3*i;
            base_idx + 2 < |lines| &&
            IsValidString(lines[base_idx]) &&
            IsValidInteger(lines[base_idx + 1]) &&
            IsValidIntegerArray(lines[base_idx + 2]) &&
            var s := lines[base_idx];
            var m := StringToInt(lines[base_idx + 1]);
            var b_array := ParseIntegerArray(lines[base_idx + 2]);
            1 <= |s| <= 50 &&
            (forall j :: 0 <= j < |s| ==> 'a' <= s[j] <= 'z') &&
            1 <= m <= |s| &&
            |b_array| == m &&
            forall k :: 0 <= k < m ==> 0 <= b_array[k] <= 1225
}

predicate ValidOutputFormat(output: string, input: string)
    requires ValidInputFormat(input)
{
    var test_cases := GetTestCases(input);
    |test_cases| > 0 ==> 
    exists output_lines: seq<string> ::
        output_lines == SplitLines(output) &&
        |output_lines| >= |test_cases| &&
        forall i :: 0 <= i < |test_cases| ==> 
            var (s, m, b) := test_cases[i];
            i < |output_lines| &&
            |output_lines[i]| == m &&
            forall j :: 0 <= j < |output_lines[i]| ==> 'a' <= output_lines[i][j] <= 'z'
}

predicate OutputSatisfiesConstraints(output: string, input: string)
    requires ValidInputFormat(input)
{
    var test_cases := GetTestCases(input);
    var output_lines := SplitLines(output);
    |test_cases| > 0 && |output_lines| >= |test_cases| ==>
    forall i :: 0 <= i < |test_cases| ==> 
        var (s, m, b) := test_cases[i];
        i < |output_lines| &&
        var t := output_lines[i];
        |t| == m &&
        (forall j :: 0 <= j < m ==> 
            b[j] == SumDistancesToGreaterChars(t, j))
}

predicate PreservesCharacterUsage(output: string, input: string)
    requires ValidInputFormat(input)
{
    var test_cases := GetTestCases(input);
    var output_lines := SplitLines(output);
    |test_cases| > 0 && |output_lines| >= |test_cases| ==>
    forall i :: 0 <= i < |test_cases| ==> 
        var (s, m, b) := test_cases[i];
        i < |output_lines| &&
        var t := output_lines[i];
        forall c :: 'a' <= c <= 'z' ==> CountChar(t, c) <= CountChar(s, c)
}

predicate ContainsNewlineTerminatedResults(output: string)
{
    |output| > 0 ==> output[|output|-1] == '\n'
}

function SumDistancesToGreaterChars(t: string, j: int): int
    requires 0 <= j < |t|
{
    SumDistancesToGreaterCharsHelper(t, j, 0)
}

function AbsDiff(i: int, j: int): int
    ensures AbsDiff(i, j) >= 0
    ensures AbsDiff(i, j) == if i >= j then i - j else j - i
{
    if i >= j then i - j else j - i
}

// <vc-helpers>
function SplitLines(s: string): seq<string>
{
  if |s| == 0 then [] else [s]
}

predicate IsValidInteger(s: string)
{
  true
}

function StringToInt(s: string): int
{
  0
}

predicate IsValidString(s: string)
{
  true
}

predicate IsValidIntegerArray(s: string)
{
  true
}

function ParseIntegerArray(s: string): seq<int>
{
  []
}

function GetTestCases(input: string): seq<(string, int, seq<int>)>
{
  []
}

function CountChar(s: string, c: char): int
{
  0
}

function SumDistancesToGreaterCharsHelper(t: string, j: int, k: int): int
    requires 0 <= j < |t|
    requires 0 <= k <= |t|
    decreases |t| - k
{
    if k == |t| then 0
    else (if t[k] > t[j] then AbsDiff(k, j) else 0) + SumDistancesToGreaterCharsHelper(t, j, k + 1)
}

function Alphabet(): string
{
  "abcdefghijklmnopqrstuvwxyz"
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires ValidInputFormat(stdin_input)
    ensures ValidOutputFormat(result, stdin_input)
    ensures OutputSatisfiesConstraints(result, stdin_input)
    ensures PreservesCharacterUsage(result, stdin_input)
    ensures result != "" ==> ContainsNewlineTerminatedResults(result)
// </vc-spec>
// <vc-code>
{
  var test_cases := GetTestCases(stdin_input);
  var out := "";
  var n := |test_cases|;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
  {
    var s, m, b := test_cases[i];
    // counts of available characters from s
    var cnt := new int[26];
    var idx := 0;
    while idx < |s|
      invariant 0 <= idx <= |s|
      invariant forall k :: 0 <= k < 26 ==> cnt[k] >= 0
    {
      cnt[ (s[idx] - 'a') ] := cnt[ (s[idx] - 'a') ] + 1;
      idx := idx + 1;
    }

    var assignedArr := new bool[m];
    var tchars := new char[m];
    var rem := m;
    var barr := new int[m];
    var k2 := 0;
    while k2 < m
      invariant 0 <= k2 <= m
    {
      barr[k2] := b[k2];
      k2 := k2 + 1;
    }

    while rem > 0
      invariant 0 <= rem <= m
      invariant forall p :: 0 <= p < m ==> assignedArr[p] ==> ('a' <= tchars[p] <= 'z')
    {
      // collect zero positions
      var zeros: seq<int> := [];
      var j := 0;
      while j < m
        invariant 0 <= j <= m
        invariant forall q :: 0 <= q < m ==> assignedArr[q] || 0 <= barr[q]
      {
        if !assignedArr[j] && barr[j] == 0 {
          zeros := zeros + [j];
        }
        j := j + 1;
      }
      var need := |zeros|;
      // find largest character with enough count
      var letter := 25;
      while letter >= 0 && cnt[letter] < need
        invariant -1 <= letter <= 25
      {
        letter := letter - 1;
      }
      // assign that letter
      var zidx := 0;
      while zidx < |zeros|
        invariant 0 <= zidx <= |zeros|
      {
        var pos := zeros[zidx];
        assignedArr[pos] := true;
        tchars[pos] := Alphabet()[letter];
        zidx := zidx + 1;
      }
      cnt[letter] := cnt[letter] - need;
      rem := rem - need;
      // update barr for unassigned positions
      var p := 0;
      while p < m
        invariant 0 <= p <= m
      {
        if !assignedArr[p] {
          var z2 := 0;
          while z2 < |zeros|
            invariant 0 <= z2 <= |zeros|
          {
            barr[p] := barr[p] - AbsDiff(p, zeros[z2]);
            z2 := z2 + 1;
          }
        }
        p := p + 1;
      }
    }

    // build line string from tchars
    var line := "";
    var pos2 := 0;
    while pos2 < m
      invariant 0 <= pos2 <= m
      invariant forall q :: 0 <= q < pos2 ==> 'a' <= tchars[q] <= 'z'
    {
      // append character as a single-element sequence to the string (strings are seq<char>)
      line := line + [tchars[pos2]];
      pos2 := pos2 + 1;
    }

    out := out + line + "\n";
    i := i + 1;
  }
  result := out;
}
// </vc-code>

