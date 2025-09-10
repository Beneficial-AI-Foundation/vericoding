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
    ensures forall line :: line in SplitByNewline(s) ==> |line| >= 0
    ensures |SplitByNewline(s)| > 0

function SplitBySpace(s: string): seq<string>
    ensures forall part :: part in SplitBySpace(s) ==> |part| >= 0
    ensures |SplitBySpace(s)| >= 2

lemma SplitBySpaceLemma(s: string)
    requires ValidTestCaseLine(s)
    ensures exists parts :: |parts| >= 2 && IsValidInteger(parts[0]) && IsValidInteger(parts[1])

lemma ValidInputLemma(input: string)
    requires ValidInput(input)
    ensures |input| > 0 && 
            |SplitByNewline(input)| >= 1 &&
            IsValidInteger(SplitByNewline(input)[0]) &&
            StringToIntVal(SplitByNewline(input)[0]) >= 0 &&
            |SplitByNewline(input)| >= StringToIntVal(SplitByNewline(input)[0]) + 1

lemma ValidTestCaseLineLemma(line: string, n: int, k: int)
    requires ValidTestCaseLine(line)
    requires SplitBySpace(line)[0] == s && SplitBySpace(line)[1] == t
    ensures n == StringToIntVal(s) && k == StringToIntVal(t) && n > 0 && k > 0 && k <= 26

function seq_from_fn<T(==)>(f: int -> T, n: int): seq<T>
    requires n >= 0
    ensures |seq_from_fn(f, n)| == n
    ensures forall j :: 0 <= j < n ==> seq_from_fn(f, n)[j] == f(j)

function StringFromSeq(seq: seq<char>): string
    ensures |StringFromSeq(seq)| == |seq|
{
    if seq == [] then
        ""
    else if |seq| == 1 then
        [seq[0]]
    else
        [seq[0]] + StringFromSeq(seq[1..])
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
  var test_count := StringToIntVal(lines[0]);
  result := "";
  var i := 1;
  
  while i <= test_count && i < |lines|
    invariant i >= 1
    invariant |result| >= 0
  {
    if ValidTestCaseLine(lines[i]) {
      var parts := SplitBySpace(lines[i]);
      var n := StringToIntVal(parts[0]);
      var k := StringToIntVal(parts[1]);
      
      var output_seq := seq_from_fn((j: int) => ((j % k) + 97) as char, n);
      var output_string := StringFromSeq(output_seq);
      
      if |result| > 0 {
        result := result + "\n";
      }
      result := result + output_string;
    }
    i := i + 1;
  }
}
// </vc-code>

