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
function ArrayToSeq<T>(a: array<T>): seq<T>
  requires a != null
{
  seq(a.Length, i => a[i])
}

function JoinChars(chars: seq<char>): string
{
  if |chars| == 0 then ""
  else [chars[0]] + JoinChars(chars[1..])
}

function SumDistancesToGreaterCharsHelper(t: string, j: int, start: int): int
  requires 0 <= j < |t| && 0 <= start <= |t|
  decreases |t| - start
{
  if start == |t| then 0
  else if start == j then SumDistancesToGreaterCharsHelper(t, j, start+1)
  else if t[start] > t[j] then AbsDiff(start, j) + SumDistancesToGreaterCharsHelper(t, j, start+1)
  else SumDistancesToGreaterCharsHelper(t, j, start+1)
}

function ConstructString(s: string, m: int, b: seq<int>): string
  requires 1 <= |s| <= 50
  requires (forall j :: 0 <= j < |s| ==> 'a' <= s[j] <= 'z')
  requires 1 <= m <= |s|
  requires |b| == m
  requires forall k :: 0 <= k < m ==> 0 <= b[k] <= 1225
  ensures |ConstructString(s, m, b)| == m
  ensures forall j :: 0 <= j < m ==> 'a' <= ConstructString(s, m, b)[j] <= 'z'
  ensures forall c :: 'a' <= c <= 'z' ==> CountChar(ConstructString(s, m, b), c) <= CountChar(s, c)
  ensures forall j :: 0 <= j < m ==> b[j] == SumDistancesToGreaterChars(ConstructString(s, m, b), j)
{
  var positions := seq(int i | 0 <= i < m :: i);
  var sorted_positions := SortByBValues(positions, b);
  var char_freq := map c | 'a' <= c <= 'z' :: StringToInt(CountChar(s, c));
  var t_arr := new char[m](_ => 'a');
  var freq := char_freq;
  for p := 0 to m-1
    invariant 0 <= p <= m
    invariant forall j :: 0 <= j < p ==> 'a' <= t_arr[j] <= 'z'
    invariant forall j :: 0 <= j < p ==> CountChar(seq(k | 0 <= k < p :: t_arr[k]), t_arr[j]) <= CountChar(s, t_arr[j])
  {
    var pos := sorted_positions[p];
    var chosen_c := FindLargestAvailable(freq);
    t_arr[pos] := chosen_c;
    freq := freq[chosen_c := freq[chosen_c] - 1];
  }
  var t_seq := seq(k | 0 <= k < m :: t_arr[k]);
  JoinChars(t_seq)
}

function SortByBValues(pos: seq<int>, b: seq<int>): seq<int>
  decreases |pos|
  requires |pos| == |b|
{
  if |pos| <= 1 then pos
  else
    var pivot := b[pos[|pos|/2]];
    var left := [];
    var equal := [];
    var right := [];
    for i: int | 0 <= i < |pos|
      invariant left + equal + right == pos[..i]
    {
      var p := pos[i];
      if b[p] > pivot then left := left + [p];
      else if b[p] == pivot then equal := equal + [p];
      else right := right + [p];
    }
    SortByBValues(left, b) + equal + SortByBValues(right, b)
}

function FindLargestAvailable(freq: map<char, int>): char
  requires exists c :: 'a' <= c <= 'z' && freq.get(c, 0) > 0
  ensures 'a' <= FindLargestAvailable(freq) <= 'z' && freq.get(FindLargestAvailable(freq), 0) > 0
{
  var c := 'z';
  while c >= 'a' && freq.get(c, 0) <= 0
    decreases (c as int) - ('a' as int)
  {
    c := ((c as int) - 1) as char;
  }
  c
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
  var lines := SplitLines(stdin_input);
  var t := StringToInt(lines[0]);
  var result_parts := new string[t](_ => "");
  for i: int := 0 to t
// </vc-code>

