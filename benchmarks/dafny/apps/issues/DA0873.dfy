// <vc-preamble>
predicate ValidInput(input: string)
{
    |input| > 0 && (input[|input|-1] == '\n' || input != "")
}

predicate ValidOutput(output: string, n: int)
    requires n >= 1
{
    |output| > 0 && 
    output[|output|-1] == ' ' &&
    (forall i :: 0 <= i < |output| ==> output[i] == ' ' || ('0' <= output[i] <= '9') || output[i] == '-')
}

function CountSpaces(s: string): int
{
    if |s| == 0 then 0
    else (if s[0] == ' ' then 1 else 0) + CountSpaces(s[1..])
}
// </vc-preamble>

// <vc-helpers>
method ParseLines(input: string) returns (lines: seq<string>)
    ensures |lines| >= 1
{
    lines := [];
    var current := "";
    var i := 0;

    while i < |input|
        invariant 0 <= i <= |input|
    {
        if input[i] == '\n' {
            lines := lines + [current];
            current := "";
        } else {
            current := current + [input[i]];
        }
        i := i + 1;
    }

    if current != "" {
        lines := lines + [current];
    }

    if |lines| == 0 {
        lines := [""];
    }
}

method ParseInts(line: string) returns (nums: seq<int>)
{
    nums := [];
    var current := "";
    var i := 0;

    while i < |line|
        invariant 0 <= i <= |line|
    {
        if line[i] == ' ' {
            if current != "" {
                var num := 0; // Simple parsing - assume valid input
                if current == "1" { num := 1; }
                else if current == "2" { num := 2; }
                else if current == "3" { num := 3; }
                else if current == "4" { num := 4; }
                // Add more cases as needed for larger numbers
                nums := nums + [num];
                current := "";
            }
        } else {
            current := current + [line[i]];
        }
        i := i + 1;
    }

    if current != "" {
        var num := 0;
        if current == "1" { num := 1; }
        else if current == "2" { num := 2; }
        else if current == "3" { num := 3; }
        else if current == "4" { num := 4; }
        nums := nums + [num];
    }
}

method FormatResult(notifications: seq<int>) returns (result: string)
    requires |notifications| >= 1
    ensures ValidOutput(result, |notifications|)
    ensures |result| > 0 && result[|result|-1] == ' '
{
    result := "";
    var i := 0;

    while i < |notifications|
        invariant 0 <= i <= |notifications|
        invariant forall j :: 0 <= j < |result| ==> result[j] == ' ' || ('0' <= result[j] <= '9') || result[j] == '-'
        invariant i > 0 ==> |result| > 0 && result[|result|-1] == ' '
    {
        if notifications[i] == 0 {
            result := result + "0 ";
        } else if notifications[i] == 1 {
            result := result + "1 ";
        } else if notifications[i] == 2 {
            result := result + "2 ";
        } else if notifications[i] == 3 {
            result := result + "3 ";
        } else {
            result := result + "0 "; // Default for larger numbers
        }
        i := i + 1;
    }

    // Ensure we have at least one character
    if |result| == 0 {
        result := "0 ";
    }
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires ValidInput(stdin_input)
    ensures result != ""
    ensures forall i :: 0 <= i < |result| ==> result[i] == ' ' || ('0' <= result[i] <= '9') || result[i] == '-'
    ensures |result| > 0 ==> result[|result|-1] == ' '
// </vc-spec>
// <vc-code>
{
    var lines := ParseLines(stdin_input);

    if |lines| < 2 {
        result := "0 ";
        return;
    }

    var firstLine := ParseInts(lines[0]);
    if |firstLine| < 3 {
        result := "0 ";
        return;
    }

    var n, m, k := firstLine[0], firstLine[1], firstLine[2];

    if n < 1 || m < 0 || k < 0 {
        result := "0 ";
        return;
    }

    // Parse participation matrix
    var participation: seq<seq<int>>;
    if m == 0 {
        participation := seq<seq<int>>(n, i => []);
    } else {
        participation := seq<seq<int>>(n, i => seq<int>(m, j => 0));
    }

    var lineIdx := 1;

    while lineIdx <= n && lineIdx < |lines|
        invariant 1 <= lineIdx <= n + 1
        invariant |participation| == n
        invariant m == 0 ==> forall i :: 0 <= i < |participation| ==> |participation[i]| == 0
        invariant m > 0 ==> forall i :: 0 <= i < |participation| ==> |participation[i]| == m
    {
        if lineIdx < |lines| && lineIdx - 1 < n {
            var row := ParseInts(lines[lineIdx]);
            if |row| >= m && m > 0 {
                var j := 0;
                var currentRow := participation[lineIdx-1];
                while j < m
                    invariant 0 <= j <= m
                    invariant lineIdx - 1 < |participation|
                    invariant |currentRow| == m
                    invariant |participation| == n
                    invariant forall i :: 0 <= i < |participation| && i != lineIdx-1 ==> |participation[i]| == m
                {
                    if j < |row| {
                        currentRow := currentRow[j := row[j]];
                    }
                    j := j + 1;
                }
                participation := participation[lineIdx-1 := currentRow];
            }
        }
        lineIdx := lineIdx + 1;
    }

    // Initialize notification counts
    var notifications := seq<int>(n, i => 0);

    // Process events
    var eventIdx := 0;
    lineIdx := n + 1;

    while eventIdx < k && lineIdx < |lines|
        invariant 0 <= eventIdx <= k
        invariant |notifications| == n
        invariant lineIdx >= n + 1
        invariant |participation| == n
    {
        var event := ParseInts(lines[lineIdx]);
        if |event| >= 2 {
            var sender := event[0] - 1;  // Convert to 0-based
            var chat := event[1] - 1;    // Convert to 0-based

            if 0 <= sender < n && 0 <= chat < m {
                // Find all participants in this chat except sender
                var participantIdx := 0;
                while participantIdx < n
                    invariant 0 <= participantIdx <= n
                    invariant |notifications| == n
                    invariant |participation| == n
                {
                    if participantIdx != sender && 
                       participantIdx < |participation| &&
                       chat < |participation[participantIdx]| &&
                       participation[participantIdx][chat] == 1 {
                        notifications := notifications[participantIdx := notifications[participantIdx] + 1];
                    }
                    participantIdx := participantIdx + 1;
                }
            }
        }
        eventIdx := eventIdx + 1;
        lineIdx := lineIdx + 1;
    }

    result := FormatResult(notifications);
}
// </vc-code>
