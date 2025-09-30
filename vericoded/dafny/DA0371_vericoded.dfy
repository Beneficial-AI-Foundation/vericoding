predicate ValidInput(input: string)
{
    |input| > 0 && 
    var lines := SplitLinesFunc(input);
    |lines| >= 2 && 
    StringToIntFunc(lines[0]) >= 1 &&
    StringToIntFunc(lines[0]) <= |lines| - 1
}

function GetFaces(polyhedron: string): int
    ensures GetFaces(polyhedron) >= 0
    ensures polyhedron == "Tetrahedron" ==> GetFaces(polyhedron) == 4
    ensures polyhedron == "Cube" ==> GetFaces(polyhedron) == 6
    ensures polyhedron == "Octahedron" ==> GetFaces(polyhedron) == 8
    ensures polyhedron == "Dodecahedron" ==> GetFaces(polyhedron) == 12
    ensures polyhedron == "Icosahedron" ==> GetFaces(polyhedron) == 20
    ensures polyhedron != "Tetrahedron" && polyhedron != "Cube" && polyhedron != "Octahedron" && polyhedron != "Dodecahedron" && polyhedron != "Icosahedron" ==> GetFaces(polyhedron) == 0
{
    if polyhedron == "Tetrahedron" then 4
    else if polyhedron == "Cube" then 6
    else if polyhedron == "Octahedron" then 8
    else if polyhedron == "Dodecahedron" then 12
    else if polyhedron == "Icosahedron" then 20
    else 0
}

function SplitLinesFunc(s: string): seq<string>
    requires |s| > 0
    ensures |SplitLinesFunc(s)| >= 0
{
    SplitLinesHelper(s, 0, 0, [])
}

function SplitLinesHelper(s: string, start: int, i: int, acc: seq<string>): seq<string>
    requires 0 <= start <= i <= |s|
    requires start <= |s|
    decreases |s| - i
{
    if i >= |s| then
        if start < |s| then acc + [s[start..|s|]]
        else acc
    else if s[i] == '\n' then
        var newAcc := if start <= i then acc + [s[start..i]] else acc;
        SplitLinesHelper(s, i + 1, i + 1, newAcc)
    else
        SplitLinesHelper(s, start, i + 1, acc)
}

function StringToIntFunc(s: string): int
    ensures StringToIntFunc(s) >= 0
{
    var trimmed := TrimFunc(s);
    if |trimmed| == 0 then 0
    else StringToIntHelper(trimmed, 0, 0)
}

function StringToIntHelper(s: string, i: int, acc: int): int
    requires 0 <= i <= |s|
    requires acc >= 0
    ensures StringToIntHelper(s, i, acc) >= acc
    ensures StringToIntHelper(s, i, acc) >= 0
    decreases |s| - i
{
    if i >= |s| then acc
    else if '0' <= s[i] <= '9' then
        StringToIntHelper(s, i + 1, acc * 10 + (s[i] as int - '0' as int))
    else
        StringToIntHelper(s, i + 1, acc)
}

function IntToStringFunc(n: int): string
    requires n >= 0
    ensures |IntToStringFunc(n)| > 0
{
    if n == 0 then "0"
    else IntToStringHelper(n)
}

function IntToStringHelper(n: int): string
    requires n > 0
    ensures |IntToStringHelper(n)| > 0
    decreases n
{
    if n < 10 then 
        [((n + ('0' as int)) as char)]
    else 
        IntToStringHelper(n / 10) + [((n % 10 + ('0' as int)) as char)]
}

function TrimFunc(s: string): string
    ensures |TrimFunc(s)| <= |s|
{
    var start := TrimStart(s, 0);
    var end := TrimEnd(s, |s|, start);
    if start < end then s[start..end] else ""
}

function TrimStart(s: string, i: int): int
    requires 0 <= i <= |s|
    ensures TrimStart(s, i) >= i
    ensures TrimStart(s, i) <= |s|
    decreases |s| - i
{
    if i >= |s| then i
    else if s[i] == ' ' || s[i] == '\t' || s[i] == '\r' || s[i] == '\n' then
        TrimStart(s, i + 1)
    else i
}

function TrimEnd(s: string, j: int, start: int): int
    requires 0 <= start <= j <= |s|
    ensures start <= TrimEnd(s, j, start) <= j
    decreases j - start
{
    if j <= start then start
    else if s[j-1] == ' ' || s[j-1] == '\t' || s[j-1] == '\r' || s[j-1] == '\n' then
        TrimEnd(s, j - 1, start)
    else j
}

function ComputeTotalUpTo(lines: seq<string>, count: int): int
    requires |lines| >= 1
    requires count >= 0
    ensures ComputeTotalUpTo(lines, count) >= 0
{
    if count == 0 then 0
    else if count >= |lines| then 0
    else GetFaces(TrimFunc(lines[count])) + ComputeTotalUpTo(lines, count - 1)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures |result| > 0
    ensures result[|result|-1] == '\n'
    ensures exists totalFaces: int :: totalFaces >= 0 && result == IntToStringFunc(totalFaces) + "\n"
    ensures ValidInput(input) ==> 
        (var lines := SplitLinesFunc(input);
         var n := StringToIntFunc(lines[0]);
         var expectedTotal := ComputeTotalUpTo(lines, n);
         result == IntToStringFunc(expectedTotal) + "\n")
// </vc-spec>
// <vc-code>
{
    var lines := SplitLinesFunc(input);
    var n := StringToIntFunc(lines[0]);
    var totalFaces := ComputeTotalUpTo(lines, n);
    result := IntToStringFunc(totalFaces) + "\n";
}
// </vc-code>

