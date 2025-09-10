predicate ValidInput(input: string)
{
    |input| > 0
}

function CanMakeSum(n: int, l: int, r: int): bool
{
    l > 0 && l <= r && n > 0 && n % l <= (r - l) * (n / l)
}

predicate ValidOutput(result: string)
{
    |result| >= 0 && forall i :: 0 <= i < |result| ==> result[i] in "Yes\nNo\n "
}

predicate CorrectSolution(input: string, result: string)
{
    var lines := SplitLines(input);
    |lines| > 0 ==> 
    (var t := ParseInt(lines[0]);
     var outputLines := SplitLines(result);
     |outputLines| >= 1 && (|outputLines| == 1 ==> outputLines[0] == "") &&
     (|outputLines| > 1 ==> outputLines[|outputLines|-1] == "") &&
     forall i :: 1 <= i <= t && i < |lines| ==>
        (var parts := SplitSpaces(lines[i]);
         |parts| >= 3 ==>
         (var n := ParseInt(parts[0]);
          var l := ParseInt(parts[1]);
          var r := ParseInt(parts[2]);
          var expectedOutput := if CanMakeSum(n, l, r) then "Yes" else "No";
          i-1 < |outputLines| && outputLines[i-1] == expectedOutput)))
}

// <vc-helpers>
function SplitLines(s: string): seq<string>
{
  if s == "" then
    []
  else if s.Contains('\n') then
    [s.Substring(0, s.IndexOf('\n'))] + SplitLines(s.Substring(s.IndexOf('\n') + 1))
  else
    [s]
}

function SplitSpaces(s: string): seq<string>
{
  if s == "" then
    []
  else if s.Contains(' ') then
    [s.Substring(0, s.IndexOf(' '))] + SplitSpaces(s.Substring(s.IndexOf(' ') + 1))
  else
    [s]
}

function ParseInt(s: string): int
  reads {}
  ensures exists i :: i == ParseInt(s)
{
  if s == "" then 0 // Or some error handling, for this problem, assume valid int strings
  else
    (var sign := 1;
     var startIndex := 0;
     if s[0] == '-' then (sign := -1; startIndex := 1) else if s[0] == '+' then startIndex := 1;
     var value := 0;
     while startIndex < |s|
       invariant 0 <= startIndex <= |s|
       invariant value >= 0
     {
       value := value * 10 + (s[startIndex] - '0');
       startIndex := startIndex + 1;
     }
     sign * value)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures ValidOutput(result)
    ensures CorrectSolution(input, result)
// </vc-spec>
// <vc-code>
{
    var lines := SplitLines(input);
    var t := ParseInt(lines[0]);
    var outputSeq: seq<string> := [];

    var i := 1;
    while i <= t
        invariant 1 <= i <= t + 1
        invariant |outputSeq| == i - 1
        invariant forall k :: 0 <= k < |outputSeq| ==> (outputSeq[k] == "Yes" || outputSeq[k] == "No")
        invariant i <= |lines| ==> (
            var parts := SplitSpaces(lines[i]);
            (|parts| >= 3 ==>
                var n := ParseInt(parts[0]);
                var l := ParseInt(parts[1]);
                var r := ParseInt(parts[2]);
                var expected := if CanMakeSum(n, l, r) then "Yes" else "No";
                var tempOutputSeq := outputSeq + [expected];
                CanMakeSum(n, l, r) == (tempOutputSeq[i-1] == "Yes")
            )
        )
        // Correctness of previous iterations for the outputSeq
        invariant forall k :: 1 <= k < i && k < |lines| ==> (
             var partsK := SplitSpaces(lines[k]);
             (|partsK| >= 3 ==>
              var nK := ParseInt(partsK[0]);
              var lK := ParseInt(partsK[1]);
              var rK := ParseInt(partsK[2]);
              (outputSeq[k-1] == (if CanMakeSum(nK, lK, rK) then "Yes" else "No"))
             )
        )
    {
        if i < |lines|
        {
            var parts := SplitSpaces(lines[i]);
            var n := ParseInt(parts[0]);
            var l := ParseInt(parts[1]);
            var r := ParseInt(parts[2]);

            if CanMakeSum(n, l, r) then
                outputSeq := outputSeq + ["Yes"];
            else
                outputSeq := outputSeq + ["No"];
        } else {
            // This case should ideally not happen if t is within valid bounds of lines.
            // For robust error handling, one might append an empty string or specific error.
            // As per problem constraints, assuming valid t based on lines.
             outputSeq := outputSeq + ["No"]; // or some default to maintain length
        }
        i := i + 1;
    }

    if |outputSeq| == 0 then
        result := ""
    else
        result := (outputSeq + [""]).ToSeq() * "\n";

    // Ensure the postcondition for ValidOutput is met
    assert |result| >= 0;
    assert forall char_i :: 0 <= char_i < |result| ==> result[char_i] in "Yes\nNo\n ";

    // Ensure the postcondition for CorrectSolution is met
    assert |lines| > 0;
    assert t == ParseInt(lines[0]);
    assert |outputSeq| == t; // Check this based on loop invariant, should be fine.
    // The final "CorrectSolution" part requires outputLines have "" at the end if not empty
    var outputLines := SplitLines(result);
    // This depends on the behavior of SplitLines and the formation of 'result'.
    // If outputSeq is not empty, result ends with "\n", so SplitLines will produce an empty string at the end.
    // If outputSeq is empty, result is "", then SplitLines yields [""].
    if |outputSeq| == 0 {
      assert outputLines == [""];
    } else {
      assert |outputLines| == |outputSeq| + 1;
      assert outputLines[|outputLines|-1] == "";
      assert forall k :: 0 <= k < |outputSeq| ==> outputLines[k] == outputSeq[k];
    }
}
// </vc-code>

