Two players alternate turns removing consecutive identical letters from a string.
The player who cannot make a move loses. Determine if the first player wins.

function countMaxMoves(s: string): nat
{
    if |s| == 0 then 0
    else 
        var stack := [];
        var moves := 0;
        countMaxMovesHelper(s, 0, stack, moves)
}

function countMaxMovesHelper(s: string, i: nat, stack: seq<char>, moves: nat): nat
    requires i <= |s|
    decreases |s| - i
{
    if i == |s| then moves
    else if |stack| > 0 && s[i] == stack[|stack| - 1] then
        countMaxMovesHelper(s, i + 1, stack[..|stack| - 1], moves + 1)
    else
        countMaxMovesHelper(s, i + 1, stack + [s[i]], moves)
}

method solve(s: string) returns (result: string)
    requires |s| >= 1
    ensures result == "Yes" || result == "No"
    ensures result == "Yes" <==> countMaxMoves(s) % 2 == 1
    ensures result == "No" <==> countMaxMoves(s) % 2 == 0
{
    var stack: seq<char> := [];
    var moves := 0;

    for i := 0 to |s|
        invariant countMaxMovesHelper(s, i, stack, moves) == countMaxMovesHelper(s, 0, [], 0)
    {
        if |stack| > 0 && s[i] == stack[|stack| - 1] {
            stack := stack[..|stack| - 1];  // pop
            moves := moves + 1;
        } else {
            stack := stack + [s[i]];  // push
        }
    }

    assert moves == countMaxMoves(s);

    if moves % 2 == 0 {
        result := "No";
    } else {
        result := "Yes";
    }
}
