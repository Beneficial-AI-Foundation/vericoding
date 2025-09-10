predicate ValidInput(n: int, s: string)
{
    n >= 0 && |s| == n && forall i :: 0 <= i < |s| ==> s[i] == 'U' || s[i] == 'R'
}

function CountKingdomTransitions(s: string): int
    requires forall i :: 0 <= i < |s| ==> s[i] == 'U' || s[i] == 'R'
    ensures CountKingdomTransitions(s) >= 0
    ensures CountKingdomTransitions(s) <= |s|
{
    if |s| == 0 then 0
    else CountTransitionsHelper(s, 0, 0, 0, -1)
}

function CountTransitionsHelper(s: string, pos: int, x: int, y: int, pred: int): int
    requires 0 <= pos <= |s|
    requires forall i :: 0 <= i < |s| ==> s[i] == 'U' || s[i] == 'R'
    requires pred == -1 || pred == 0 || pred == 1
    ensures CountTransitionsHelper(s, pos, x, y, pred) >= 0
    ensures CountTransitionsHelper(s, pos, x, y, pred) <= |s| - pos
    decreases |s| - pos
{
    if pos == |s| then 0
    else
        var newX := if s[pos] == 'U' then x else x + 1;
        var newY := if s[pos] == 'U' then y + 1 else y;

        if newX == newY then
            CountTransitionsHelper(s, pos + 1, newX, newY, pred)
        else
            var cur := if newX > newY then 0 else 1;
            var transition := if cur != pred && pred != -1 then 1 else 0;
            transition + CountTransitionsHelper(s, pos + 1, newX, newY, cur)
}

// <vc-helpers>
lemma CountTransitionsHelperCorrectness(s: string, pos: int, x: int, y: int, pred: int)
    requires 0 <= pos <= |s|
    requires forall i :: 0 <= i < |s| ==> s[i] == 'U' || s[i] == 'R'
    requires pred == -1 || pred == 0 || pred == 1
    ensures CountTransitionsHelper(s, pos, x, y, pred) >= 0
    ensures CountTransitionsHelper(s, pos, x, y, pred) <= |s| - pos
    decreases |s| - pos
{
    // This lemma helps establish the properties of CountTransitionsHelper
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, s: string) returns (result: int)
    requires ValidInput(n, s)
    ensures result >= 0
    ensures result <= n
    ensures n == 0 ==> result == 0
    ensures result == CountKingdomTransitions(s)
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        return 0;
    }
    
    var pos := 0;
    var x := 0;
    var y := 0;
    var pred := -1;
    var transitions := 0;
    
    while pos < n
        invariant 0 <= pos <= n
        invariant pred == -1 || pred == 0 || pred == 1
        invariant transitions >= 0
        invariant transitions + CountTransitionsHelper(s, pos, x, y, pred) == CountKingdomTransitions(s)
    {
        var newX := if s[pos] == 'U' then x else x + 1;
        var newY := if s[pos] == 'U' then y + 1 else y;
        
        if newX == newY {
            // No state change when x == y
        } else {
            var cur := if newX > newY then 0 else 1;
            if cur != pred && pred != -1 {
                transitions := transitions + 1;
            }
            pred := cur;
        }
        
        x := newX;
        y := newY;
        pos := pos + 1;
    }
    
    result := transitions;
}
// </vc-code>

