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
lemma CountMaxMovesEquivalence(s: string)
    ensures countMaxMoves(s) == countMaxMovesIterative(s)
{
    if |s| == 0 {
        assert countMaxMoves(s) == 0;
        assert countMaxMovesIterative(s) == 0;
    } else {
        var stack := [];
        var moves := 0;
        assert countMaxMoves(s) == countMaxMovesHelper(s, 0, stack, moves);
        CountMaxMovesHelperEquivalence(s, 0, stack, moves);
    }
}

lemma CountMaxMovesHelperEquivalence(s: string, i: nat, stack: seq<char>, moves: nat)
    requires i <= |s|
    ensures countMaxMovesHelper(s, i, stack, moves) == countMaxMovesIterativeFrom(s, i, stack, moves)
    decreases |s| - i
{
    if i == |s| {
        assert countMaxMovesHelper(s, i, stack, moves) == moves;
        assert countMaxMovesIterativeFrom(s, i, stack, moves) == moves;
    } else {
        if |stack| > 0 && s[i] == stack[|stack| - 1] {
            CountMaxMovesHelperEquivalence(s, i + 1, stack[..|stack| - 1], moves + 1);
        } else {
            CountMaxMovesHelperEquivalence(s, i + 1, stack + [s[i]], moves);
        }
    }
}

function countMaxMovesIterative(s: string): nat
{
    countMaxMovesIterativeFrom(s, 0, [], 0)
}

function countMaxMovesIterativeFrom(s: string, i: nat, stack: seq<char>, moves: nat): nat
    requires i <= |s|
    decreases |s| - i
{
    if i == |s| then moves
    else if |stack| > 0 && s[i] == stack[|stack| - 1] then
        countMaxMovesIterativeFrom(s, i + 1, stack[..|stack| - 1], moves + 1)
    else
        countMaxMovesIterativeFrom(s, i + 1, stack + [s[i]], moves)
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
    var stack: seq<char> := [];
    var moves := 0;
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant countMaxMovesIterativeFrom(s, i, stack, moves) == countMaxMovesIterative(s) 
    {
        if |stack| > 0 && s[i] == stack[|stack| - 1] {
            stack := stack[..|stack| - 1];
            moves := moves + 1;
        } else {
            stack := stack + [s[i]];
        }
        i := i + 1;
    }
    
    assert i == |s|;
    assert countMaxMovesIterativeFrom(s, i, stack, moves) == moves;
    assert moves == countMaxMovesIterative(s);
    CountMaxMovesEquivalence(s);
    assert moves == countMaxMoves(s);
    
    if moves % 2 == 1 {
        result := "Yes";
    } else {
        result := "No";
    }
}
// </vc-code>

