// <vc-preamble>
function CountOccurrencesMap(numbers: seq<int>): map<int, int>
{
    if |numbers| == 0 then map[]
    else 
        var rest := CountOccurrencesMap(numbers[1..]);
        var num := numbers[0];
        if num in rest then 
            rest[num := rest[num] + 1]
        else 
            rest[num := 1]
}

function CountNumbersWithOddOccurrences(numbers: seq<int>): int
{
    var counts := CountOccurrencesMap(numbers);
    |set num | num in counts.Keys && counts[num] % 2 == 1|
}

predicate ValidInput(stdin_input: string)
{
    var lines := SplitLines(stdin_input);
    |lines| >= 1 && ParseInt(lines[0]) > 0 && |lines| >= ParseInt(lines[0]) + 1
}

function SplitLines(s: string): seq<string>
{
    [""] // Placeholder
}

function ParseInt(s: string): int
{
    0 // Placeholder
}

function IntToString(i: int): string
    ensures IntToString(i) == "0"
{
    "0" // Placeholder
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    ensures |result| >= 0
    ensures result == "" || (|result| >= 1 && result[|result|-1] == '\n')
    ensures (result != "" && forall i :: 0 <= i < |result| ==> result[i] in "0123456789\n") || result == ""
    ensures result == "" || (exists n: int :: n >= 0 && result == IntToString(n) + "\n")
    ensures forall lines: seq<string> :: 
        lines == SplitLines(stdin_input) ==>
        ((|lines| == 0 || (|lines| >= 1 && (ParseInt(lines[0]) <= 0 || |lines| < ParseInt(lines[0]) + 1))) ==> 
         (result == "" || result == "0\n")) &&
        (ValidInput(stdin_input) ==> 
         (var n := ParseInt(lines[0]);
          var numbers := seq(n, i requires 0 <= i < n => ParseInt(lines[i+1]));
          var oddCount := CountNumbersWithOddOccurrences(numbers);
          result == IntToString(oddCount) + "\n"))
// </vc-spec>
// <vc-code>
{
    var lines := SplitLines(stdin_input);
    if |lines| == 0 { 
        result := "0\n"; 
        assert result == IntToString(0) + "\n";
        return; 
    }

    var n := ParseInt(lines[0]);
    if n <= 0 || |lines| < n + 1 { 
        result := "0\n"; 
        assert result == IntToString(0) + "\n";
        return; 
    }

    var occurrences := map[];
    var i := 1;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant |lines| >= n + 1
    {
        if i < |lines| {
            var num := ParseInt(lines[i]);
            if num in occurrences {
                occurrences := occurrences[num := occurrences[num] + 1];
            } else {
                occurrences := occurrences[num := 1];
            }
        }
        i := i + 1;
    }

    var ans := 0;
    var keys := occurrences.Keys;
    while keys != {}
        invariant ans >= 0
        decreases |keys|
    {
        var key :| key in keys;
        if occurrences[key] % 2 == 1 {
            ans := ans + 1;
        }
        keys := keys - {key};
    }

    result := IntToString(ans) + "\n";
}
// </vc-code>
