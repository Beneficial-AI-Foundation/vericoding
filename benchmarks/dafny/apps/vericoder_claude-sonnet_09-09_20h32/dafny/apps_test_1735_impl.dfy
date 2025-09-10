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

// <vc-helpers>
lemma countMaxMovesCorrectness(s: string)
    ensures countMaxMoves(s) == countMaxMovesHelper(s, 0, [], 0)
{
    // This lemma is automatically proven by the definition of countMaxMoves
}

lemma countMaxMovesHelperProperties(s: string, i: nat, stack: seq<char>, moves: nat)
    requires i <= |s|
    ensures countMaxMovesHelper(s, i, stack, moves) >= moves
    decreases |s| - i
{
    if i == |s| {
        // Base case: returns moves
    } else if |stack| > 0 && s[i] == stack[|stack| - 1] {
        countMaxMovesHelperProperties(s, i + 1, stack[..|stack| - 1], moves + 1);
    } else {
        countMaxMovesHelperProperties(s, i + 1, stack + [s[i]], moves);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires |s| >= 1
    ensures result == "Yes" || result == "No"
    ensures result == "Yes" <==> countMaxMoves(s) % 2 == 1
    ensures result == "No" <==> countMaxMoves(s) % 2 == 0
// </vc-spec>
// <vc-code>
{
    var maxMoves := countMaxMoves(s);
    if maxMoves % 2 == 1 {
        result := "Yes";
    } else {
        result := "No";
    }
}
// </vc-code>

