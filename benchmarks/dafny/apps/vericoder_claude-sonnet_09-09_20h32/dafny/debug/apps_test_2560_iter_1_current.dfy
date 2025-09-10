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
    [""]
}

function SplitSpaces(s: string): seq<string>
{
    [""]
}

function ParseInt(s: string): int
{
    0
}

function JoinLines(lines: seq<string>): string
{
    ""
}

lemma SplitLinesProperties(s: string)
    ensures var lines := SplitLines(s); |lines| >= 1
    ensures var lines := SplitLines(s); |lines| > 1 ==> lines[|lines|-1] == ""
{
}

lemma ParseIntProperties(s: string)
    ensures ParseInt(s) >= 0
{
}

lemma JoinLinesProperties(lines: seq<string>)
    ensures var result := JoinLines(lines); ValidOutput(result)
    ensures var result := JoinLines(lines); var splitResult := SplitLines(result); 
            |splitResult| >= 1 && (|splitResult| == 1 ==> splitResult[0] == "") &&
            (|splitResult| > 1 ==> splitResult[|splitResult|-1] == "")
{
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
    SplitLinesProperties(input);
    
    if |lines| == 0 {
        return "";
    }
    
    var t := ParseInt(lines[0]);
    ParseIntProperties(lines[0]);
    
    var outputLines: seq<string> := [];
    var i := 1;
    
    while i <= t && i < |lines|
        invariant 1 <= i <= t + 1
        invariant |outputLines| == i - 1
        invariant forall j :: 1 <= j < i && j < |lines| ==>
            (var parts := SplitSpaces(lines[j]);
             |parts| >= 3 ==>
             (var n := ParseInt(parts[0]);
              var l := ParseInt(parts[1]);
              var r := ParseInt(parts[2]);
              var expectedOutput := if CanMakeSum(n, l, r) then "Yes" else "No";
              j-1 < |outputLines| && outputLines[j-1] == expectedOutput))
    {
        var parts := SplitSpaces(lines[i]);
        
        if |parts| >= 3 {
            var n := ParseInt(parts[0]);
            var l := ParseInt(parts[1]);
            var r := ParseInt(parts[2]);
            ParseIntProperties(parts[0]);
            ParseIntProperties(parts[1]);
            ParseIntProperties(parts[2]);
            
            var answer := if CanMakeSum(n, l, r) then "Yes" else "No";
            outputLines := outputLines + [answer];
        } else {
            outputLines := outputLines + ["No"];
        }
        
        i := i + 1;
    }
    
    outputLines := outputLines + [""];
    result := JoinLines(outputLines);
    JoinLinesProperties(outputLines);
}
// </vc-code>

