// <vc-preamble>
predicate validInputFormat(input: string)
{
    var lines := splitLinesSpec(input);
    |lines| > 0 &&
    (exists n: int :: 
        n >= 4 && n % 4 == 0 &&
        lines[0] == intToString(n) &&
        |lines| >= n + 1 &&
        (forall i :: 1 <= i <= n ==> 
            |lines[i]| == n / 4 &&
            (forall c :: c in lines[i] ==> c in "0123456789ABCDEFabcdef")))
}

function parseInputToMatrix(input: string): seq<seq<int>>
    requires validInputFormat(input)
{
    var lines := splitLinesSpec(input);
    var n := parseIntegerSpec(lines[0]);
    hexToBinaryMatrixSpec(lines[1..n+1], n)
}

predicate isValidCompression(matrix: seq<seq<int>>, n: int, x: int)
    requires |matrix| == n
    requires forall i :: 0 <= i < |matrix| ==> |matrix[i]| == n
    requires x > 0 && n % x == 0
{
    forall blockRow, blockCol :: 
        0 <= blockRow < n / x && 0 <= blockCol < n / x ==>
        isUniformBlock(matrix, blockRow * x, blockCol * x, x)
}

predicate isUniformBlock(matrix: seq<seq<int>>, startRow: int, startCol: int, size: int)
    requires |matrix| > 0
    requires forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix[0]|
    requires 0 <= startRow < |matrix| && 0 <= startCol < |matrix[0]|
    requires startRow + size <= |matrix| && startCol + size <= |matrix[0]|
{
    if size == 0 then true
    else
        var firstValue := matrix[startRow][startCol];
        forall i, j :: startRow <= i < startRow + size && startCol <= j < startCol + size ==>
            matrix[i][j] == firstValue
}

function splitLinesSpec(input: string): seq<string>
    ensures forall line :: line in splitLinesSpec(input) ==> '\n' !in line
{
    []
}

function parseIntegerSpec(s: string): int
    requires forall c :: c in s ==> c in "0123456789"
    requires |s| > 0
    ensures parseIntegerSpec(s) >= 0
{
    0
}

function hexToBinaryMatrixSpec(hexLines: seq<string>, n: int): seq<seq<int>>
    requires n >= 4 && n % 4 == 0
    requires |hexLines| == n
    requires forall line :: line in hexLines ==> |line| == n / 4
    requires forall line :: line in hexLines ==> forall c :: c in line ==> c in "0123456789ABCDEFabcdef"
    ensures |hexToBinaryMatrixSpec(hexLines, n)| == n
    ensures forall i :: 0 <= i < |hexToBinaryMatrixSpec(hexLines, n)| ==> |hexToBinaryMatrixSpec(hexLines, n)[i]| == n
    ensures forall i, j :: 0 <= i < |hexToBinaryMatrixSpec(hexLines, n)| && 0 <= j < |hexToBinaryMatrixSpec(hexLines, n)[i]| ==> hexToBinaryMatrixSpec(hexLines, n)[i][j] in {0, 1}
{
    seq(n, i => seq(n, j => 0))
}

function intToString(n: int): string
    requires n >= 0
    ensures |intToString(n)| > 0
    ensures forall c :: c in intToString(n) ==> c in "0123456789"
    ensures n == 0 <==> intToString(n) == "0"
{
    if n == 0 then "0"
    else intToStringHelper(n)
}

function intToStringHelper(n: int): string
    requires n > 0
    ensures |intToStringHelper(n)| > 0
    ensures forall c :: c in intToStringHelper(n) ==> c in "0123456789"
{
    if n < 10 then [('0' as int + n) as char]
    else intToStringHelper(n / 10) + [('0' as int + (n % 10)) as char]
}
// </vc-preamble>

// <vc-helpers>
method splitLines(input: string) returns (lines: seq<string>)
    ensures |lines| >= 0
    ensures forall line :: line in lines ==> '\n' !in line
    ensures lines == splitLinesSpec(input)
{
    lines := [];
}

method parseInteger(s: string) returns (n: int)
    ensures n >= 0
    ensures (forall c :: c in s ==> c in "0123456789") && |s| > 0 ==> n == parseIntegerSpec(s)
{
    n := 0;
}

method hexToBinaryMatrix(hexLines: seq<string>, n: int) returns (matrix: seq<seq<int>>)
    requires n >= 4 && n % 4 == 0
    requires |hexLines| == n
    requires forall line :: line in hexLines ==> |line| == n / 4
    requires forall line :: line in hexLines ==> forall c :: c in line ==> c in "0123456789ABCDEFabcdef"
    ensures |matrix| == n
    ensures forall i :: 0 <= i < |matrix| ==> |matrix[i]| == n
    ensures forall i, j :: 0 <= i < |matrix| && 0 <= j < |matrix[i]| ==> matrix[i][j] in {0, 1}
    ensures matrix == hexToBinaryMatrixSpec(hexLines, n)
{
    matrix := seq(n, i => seq(n, j => 0));
}

method findMaxCompression(matrix: seq<seq<int>>, n: int) returns (maxX: int)
    requires n >= 4 && n % 4 == 0
    requires |matrix| == n
    requires forall i :: 0 <= i < |matrix| ==> |matrix[i]| == n
    requires forall i, j :: 0 <= i < |matrix| && 0 <= j < |matrix[i]| ==> matrix[i][j] in {0, 1}
    ensures 1 <= maxX <= n
    ensures maxX > 0 && n % maxX == 0
    ensures isValidCompression(matrix, n, maxX)
    ensures forall x :: x > maxX && n % x == 0 ==> !isValidCompression(matrix, n, x)
{
    maxX := 1;
    assert isValidCompression(matrix, n, 1);

    var x := 2;
    while x <= n
        invariant 1 <= maxX <= n
        invariant maxX > 0 && n % maxX == 0
        invariant isValidCompression(matrix, n, maxX)
        invariant forall y :: maxX < y < x && n % y == 0 ==> !isValidCompression(matrix, n, y)
        invariant 2 <= x <= n + 1
    {
        if n % x == 0 && isValidCompression(matrix, n, x) {
            maxX := x;
        }
        x := x + 1;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    ensures |result| > 0
    ensures forall c :: c in result ==> c in "0123456789\n"
    ensures exists maxX: int :: maxX >= 1 && result == intToString(maxX) + "\n"
    ensures validInputFormat(stdin_input) ==> 
        (exists n: int, matrix: seq<seq<int>> :: 
            n >= 4 && n % 4 == 0 &&
            |matrix| == n &&
            (forall i :: 0 <= i < |matrix| ==> |matrix[i]| == n) &&
            (forall i, j :: 0 <= i < |matrix| && 0 <= j < |matrix[i]| ==> matrix[i][j] in
// </vc-spec>
// <vc-code>
{0, 1}
// </vc-code>
