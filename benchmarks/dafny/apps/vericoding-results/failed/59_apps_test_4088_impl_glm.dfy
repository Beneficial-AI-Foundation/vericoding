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
function SumDistancesToGreaterCharsHelper(t: string, j: int, k: int): int
    requires 0 <= j < |t|
    requires 0 <= k <= |t|
{
    if k == |t| then 0
    else if k != j && t[k] > t[j] then AbsDiff(j, k) + SumDistancesToGreaterCharsHelper(t, j, k + 1)
    else SumDistancesToGreaterCharsHelper(t, j, k + 1)
}

function CountChar(s: string, c: char): int
    requires 'a' <= c <= 'z'
{
    if |s| == 0 then 0
    else if s[0] == c then 1 + CountChar(s[1..], c)
    else CountChar(s[1..], c)
}

function GetTestCases(input: string): seq<(string, int, seq<int>)>
    requires ValidInputFormat(input)
{
    var lines := SplitLines(input);
    var t := StringToInt(lines[0]);
    var test_cases: seq<(string, int, seq<int>)> := [];
    var i := 0;
    while i < t
        invariant 0 <= i <= t
        invariant |test_cases| == i
    {
        var base_idx := 1 + 3*i;
        var s := lines[base_idx];
        var m := StringToInt(lines[base_idx + 1]);
        var b_array := ParseIntegerArray(lines[base_idx + 2]);
        test_cases := test_cases + [(s, m, b_array)];
        i := i + 1;
    }
    test_cases
}

function SplitLines(s: string): seq<string>
    ensures var lines := SplitLines(s);
        |lines| > 0 ==> (var last := lines[|lines| - 1]; last == "" || last[|last|-1] != '\n')
{
    if s == "" then [""]
    else SplitLinesHelper(s, 0, [])
}

function SplitLinesHelper(s: string, i: int, acc: seq<string>): seq<string>
    requires 0 <= i <= |s|
{
    if i == |s| then acc + [""]
    else 
        var j := i;
        while j < |s| && s[j] != '\n'
            invariant i <= j <= |s|
        {
            j := j + 1;
        }
        if j == |s| then acc + [s[i..]]
        else SplitLinesHelper(s, j + 1, acc + [s[i..j]])
}

function IsValidInteger(s: string): bool
{
    if s == "" then false
    else
        var i := 0;
        if s[0] == '-' then i := 1 else i := 0;
        if i == |s| then false
        else 
            var digits := 0;
            while i < |s|
                invariant i <= |s|
                invariant digits >= 0
            {
                if '0' <= s[i] <= '9' then digits := digits + 1
                else return false;
                i := i + 1;
            }
            digits > 0
}

function IsValidString(s: string): bool
{
    forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
}

function IsValidIntegerArray(s: string): bool
{
    if s == "" then false
    else
        var elements := 0;
        var i := 0;
        while i < |s|
            invariant 0 <= i <= |s|
            invariant elements >= 0
        {
            if '0' <= s[i] <= '9' then
                while i < |s| && '0' <= s[i] <= '9'
                    invariant i <= |s|
                {
                    i := i + 1;
                }
                elements := elements + 1;
                if i < |s| && s[i] == ' ' then i := i + 1
                else if i < |s| then return false;
            else return false;
        }
        elements > 0
}

function StringToInt(s: string): int
    requires IsValidInteger(s)
{
    StringToIntHelper(s, 0)
}

function StringToIntHelper(s: string, i: int): int
    requires 0 <= i <= |s|
    requires IsValidInteger(s)
{
    if i == |s| then 0
    else 
        var digit := ord(s[i]) - ord('0');
        digit + 10 * StringToIntHelper(s, i + 1)
}

function ParseIntegerArray(s: string): seq<int>
    requires IsValidIntegerArray(s)
{
    var result: seq<int> := [];
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
    {
        var j := i;
        while j < |s| && s[j] != ' '
            invariant i <= j <= |s|
        {
            j := j + 1;
        }
        var num_str := s[i..j];
        result := result + [StringToInt(num_str)];
        if j < |s| then i := j + 1 else i := j;
    }
    result
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
  var result_lines: seq<string> := [];
  var i := 0;
  
  while i < t
    invariant 0 <= i <= t
    invariant |result_lines| == i
  {
    var base_idx := 1 + 3*i;
    var s := lines[base_idx];
    var m := StringToInt(lines[base_idx + 1]);
    var b_array := ParseIntegerArray(lines[base_idx + 2]);
    
    var available_chars: seq<char> := [];
    var j := 0;
    while j < |s|
      invariant 0 <= j <= |s|
      invariant |available_chars| == j
    {
      available_chars := available_chars + [s[j]];
      j := j + 1;
    }
    
    var output_chars: seq<char> := [];
    var k := 0;
    
    while k < m
      invariant 0 <= k <= m
      invariant |output_chars| == k
      invariant forall c :: 'a' <= c <= 'z' ==> CountChar(output_chars, c) <= CountChar(s, c)
    {
      var found := false;
      var l := 0;
      while l < |available_chars| && !found
        invariant 0 <= l <= |available_chars|
        invariant !found ==> forall i :: 0 <= i < l ==> !(SumDistancesToGreaterChars(output_chars + [available_chars[i]], k) == b_array[k])
      {
        var test_char := available_chars[l];
        var test_output := output_chars + [test_char];
        if SumDistancesToGreaterChars(test_output, k) == b_array[k] then
        {
          output_chars := output_chars + [test_char];
          available_chars := available_chars[..l] + available_chars[l+1..];
          found := true;
        }
        l := l + 1;
      }
      k := k + 1;
    }
    
    var output_str := "";
    var idx := 0;
    while idx < |output_chars|
      invariant 0 <= idx <= |output_chars|
    {
      output_str := output_str + output_chars[idx];
      idx := idx + 1;
    }
    
    result_lines := result_lines + [output_str];
    i := i + 1;
  }
  
  var result_str := "";
  var line_idx := 0;
  while line_idx < |result_lines|
    invariant 0 <= line_idx <= |result_lines|
  {
    result_str := result_str + result_lines[line_idx] + "\n";
    line_idx := line_idx + 1;
  }
  
  return result_str;
}
// </vc-code>

