// <vc-preamble>
predicate ValidBoardInput(stdin_input: string)
{
    var lines := ParseInputLines(stdin_input);
    |lines| >= 1 &&
    ValidFirstLine(lines[0]) &&
    var n := StringToInt(lines[0]);
    3 <= n <= 50 &&
    |lines| == n + 1 &&
    (forall i :: 1 <= i <= n ==> |lines[i]| == n) &&
    (forall i :: 1 <= i <= n ==> forall j :: 0 <= j < n ==> lines[i][j] in {'.', '#'}) &&
    (exists i, j :: 1 <= i <= n && 0 <= j < n && lines[i][j] == '.')
}

predicate GreedyAlgorithmSucceeds(stdin_input: string)
{
    var lines := ParseInputLines(stdin_input);
    |lines| >= 1 &&
    var n := StringToInt(lines[0]);
    3 <= n <= 50 &&
    |lines| == n + 1 &&
    var initial_board := seq(n, i requires 0 <= i < n && i + 1 < |lines| => lines[i+1]);
    |initial_board| == n &&
    (forall i :: 0 <= i < n ==> |initial_board[i]| == n) &&
    (forall i :: 0 <= i < n ==> forall j :: 0 <= j < n ==> initial_board[i][j] in {'.', '#'}) &&
    GreedySimulation(initial_board, n, 0, 0)
}
// </vc-preamble>

// <vc-helpers>
function ParseInputLines(stdin_input: string): seq<string>
{
    if |stdin_input| == 0 then []
    else SplitByNewline(stdin_input)
}

function SplitByNewline(s: string): seq<string>
{
    if |s| == 0 then []
    else if s[|s|-1] == '\n' then SplitByNewlineHelper(s[..|s|-1], "", [])
    else SplitByNewlineHelper(s, "", [])
}

function SplitByNewlineHelper(s: string, current: string, acc: seq<string>): seq<string>
{
    if |s| == 0 then acc + [current]
    else if s[0] == '\n' then SplitByNewlineHelper(s[1..], "", acc + [current])
    else SplitByNewlineHelper(s[1..], current + [s[0]], acc)
}

predicate ValidFirstLine(line: string)
{
    |line| > 0 && (forall c :: c in line ==> c in "0123456789") && StringToInt(line) >= 3 && StringToInt(line) <= 50
}

function StringToInt(s: string): int
{
    if |s| == 0 then 0
    else StringToIntHelper(s, 0)
}

function StringToIntHelper(s: string, acc: int): int
{
    if |s| == 0 then acc
    else if s[0] in "0123456789" then
        var digit := (s[0] as int) - ('0' as int);
        StringToIntHelper(s[1..], acc * 10 + digit)
    else 0
}

predicate GreedySimulation(board: seq<seq<char>>, n: int, start_i: int, start_j: int)
    requires |board| == n
    requires forall i :: 0 <= i < n ==> |board[i]| == n
    requires 0 <= start_i <= n
    requires 0 <= start_j <= n
    decreases n - start_i, n - start_j
{
    if start_i >= n then true
    else if start_j >= n then GreedySimulation(board, n, start_i + 1, 0)
    else if 0 <= start_i < n && 0 <= start_j < n && board[start_i][start_j] == '#' then 
        GreedySimulation(board, n, start_i, start_j + 1)
    else if 0 <= start_i < n && 0 <= start_j < n && board[start_i][start_j] == '.' then
        if CanPlacePlusWithTopAt(board, n, start_i, start_j) then
            var new_board := PlacePlusWithTopAt(board, n, start_i, start_j);
            GreedySimulation(new_board, n, start_i, start_j + 1)
        else false
    else false
}

predicate CanPlacePlusWithTopAt(board: seq<seq<char>>, n: int, top_i: int, top_j: int)
    requires |board| == n
    requires forall i :: 0 <= i < n ==> |board[i]| == n
{
    var center_i := top_i + 1;
    var center_j := top_j;

    top_i < n - 2 && top_j < n - 1 && top_j > 0 &&
    0 <= center_i < n && 0 <= center_j < n &&
    0 <= center_i + 1 < n && 0 <= center_j - 1 < n && 0 <= center_j + 1 < n &&
    board[center_i][center_j] == '.' &&
    board[center_i + 1][center_j] == '.' &&
    board[center_i][center_j - 1] == '.' &&
    board[center_i][center_j + 1] == '.'
}

function PlacePlusWithTopAt(board: seq<seq<char>>, n: int, top_i: int, top_j: int): seq<seq<char>>
    requires |board| == n
    requires forall i :: 0 <= i < n ==> |board[i]| == n
    requires CanPlacePlusWithTopAt(board, n, top_i, top_j)
{
    var center_i := top_i + 1;
    var center_j := top_j;

    seq(n, i => 
        seq(n, j =>
            if (i == center_i && j == center_j) ||
               (i == center_i + 1 && j == center_j) ||
               (i == center_i && j == center_j - 1) ||
               (i == center_i && j == center_j + 1)
            then '#'
            else if 0 <= i < |board| && 0 <= j < |board[i]| then board[i][j]
            else '.'))
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires ValidBoardInput(stdin_input)
    ensures result == "YES\n" || result == "NO\n"
    ensures (result == "YES\n") <==> GreedyAlgorithmSucceeds(stdin_input)
// </vc-spec>
// <vc-code>
{
    if GreedyAlgorithmSucceeds(stdin_input) {
        result := "YES\n";
    } else {
        result := "NO\n";
    }
}
// </vc-code>
