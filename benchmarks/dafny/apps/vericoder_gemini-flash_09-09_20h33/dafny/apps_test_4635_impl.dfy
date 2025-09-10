predicate ValidInput(input: string)
{
    |input| > 0 && 
    (exists lines :: lines == SplitByNewline(input) && 
     |lines| >= 1 && 
     IsValidInteger(lines[0]) &&
     StringToIntVal(lines[0]) >= 0 &&
     |lines| >= StringToIntVal(lines[0]) + 1 &&
     (forall i :: 1 <= i <= StringToIntVal(lines[0]) && i < |lines| ==> ValidTestCaseLine(lines[i])))
}

predicate ValidTestCaseLine(line: string)
{
    exists parts :: (parts == SplitBySpace(line) &&
                    |parts| >= 2 &&
                    IsValidInteger(parts[0]) &&
                    IsValidInteger(parts[1]) &&
                    StringToIntVal(parts[0]) > 0 &&
                    StringToIntVal(parts[1]) > 0 &&
                    StringToIntVal(parts[1]) <= 26)
}

predicate IsValidInteger(s: string)
{
    |s| > 0 && 
    (|s| == 1 || s[0] != '0' || s == "0") &&
    forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

function StringToIntVal(s: string): int
    requires IsValidInteger(s)
    ensures StringToIntVal(s) >= 0
{
    if |s| == 0 then 0 else
    if |s| == 1 then (s[0] as int) - 48 else
    StringToIntVal(s[0..|s|-1]) * 10 + ((s[|s|-1] as int) - 48)
}

predicate CyclicPatternCorrect(n: int, k: int, output: string)
    requires n > 0 && k > 0 && k <= 26
{
    |output| == n &&
    (forall j :: 0 <= j < n ==> output[j] == ((j % k) + 97) as char)
}

// <vc-helpers>
function SplitByNewline(s: string): seq<string>
{
  if s == "" then []
  else if s contains '\n' then
    var i := s.IndexOf('\n');
    [s[..i]] + SplitByNewline(s[i+1..])
  else
    [s]
}

function SplitBySpace(s: string): seq<string>
{
  if s == "" then []
  else if s contains ' ' then
    var i := s.IndexOf(' ');
    [s[..i]] + SplitBySpace(s[i+1..])
  else
    [s]
}

function SeqToString(s: seq<string>, separator: string): string
{
  if s == [] then ""
  else if s.len == 1 then s[0]
  else s[0] + separator + SeqToString(s[1..], separator)
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires ValidInput(stdin_input)
    ensures |result| >= 0
// </vc-spec>
// <vc-code>
{
    var lines := SplitByNewline(stdin_input);
    var num_test_cases := StringToIntVal(lines[0]);
    var output_lines: seq<string> := [];

    var i := 1;
    while i <= num_test_cases
        invariant 1 <= i <= num_test_cases + 1
        invariant num_test_cases == StringToIntVal(lines[0])
        invariant |lines| >= num_test_cases + 1
        invariant forall k' :: 1 <= k' < i ==>
            (ValidTestCaseLine(lines[k']) &&
             var parts_k := SplitBySpace(lines[k']);
             var n_k := StringToIntVal(parts_k[0]);
             var k_k := StringToIntVal(parts_k[1]);
             CyclicPatternCorrect(n_k, k_k, output_lines[k'-1])
            )
        invariant |output_lines| == i - 1
        decreases num_test_cases - i
    {
        var parts := SplitBySpace(lines[i]);
        var n := StringToIntVal(parts[0]);
        var k := StringToIntVal(parts[1]);

        var current_output := "";
        var j := 0;
        while j < n
            invariant 0 <= j <= n
            invariant |current_output| == j
            invariant forall x :: 0 <= x < j ==> 'a' <= current_output[x] <= 'z'
            decreases n - j
        {
            current_output := current_output + (((j % k) + 97) as char);
            j := j + 1;
        }
        output_lines := output_lines + [current_output];
        i := i + 1;
    }

    result := SeqToString(output_lines, "\n");
}
// </vc-code>

