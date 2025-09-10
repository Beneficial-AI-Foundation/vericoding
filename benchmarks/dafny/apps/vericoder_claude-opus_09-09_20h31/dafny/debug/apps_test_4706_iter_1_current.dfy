predicate ValidInput(lines: seq<string>)
{
    |lines| == 3 && forall i :: 0 <= i < 3 ==> |lines[i]| == 3
}

function ExtractDiagonal(lines: seq<string>): string
    requires ValidInput(lines)
{
    [lines[0][0], lines[1][1], lines[2][2]]
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(lines: seq<string>) returns (result: string)
    requires ValidInput(lines)
    ensures |result| == 4
    ensures result[0] == lines[0][0]
    ensures result[1] == lines[1][1] 
    ensures result[2] == lines[2][2]
    ensures result[3] == '\n'
    ensures result == ExtractDiagonal(lines) + ['\n']
// </vc-spec>
// <vc-code>
{
    result := [lines[0][0], lines[1][1], lines[2][2], '\n'];
}
// </vc-code>

