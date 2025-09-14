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
method compute_countMaxMoves(s: string) returns (m: nat)
    ensures m == countMaxMoves(s)
{
    if |s| == 0 {
        m := 0;
        return;
    }
    var stack: seq<char> := [];
    m := 0;
    var i: nat := 0;
    while i < |s|
        invariant i <= |s|
        invariant countMaxMoves(s) == countMaxMovesHelper(s, i, stack, m)
        decreases |s| - i
    {
        if |stack| > 0 && s[i] == stack[|stack| - 1] {
            stack := stack[..|stack| - 1];
            m := m + 1;
        } else {
            stack := stack + [s[i]];
        }
        i := i + 1;
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
  var moves := compute_countMaxMoves(s);
  if moves % 2 == 1 {
    result := "Yes";
  } else {
    result := "No";
  }
}
// </vc-code>

