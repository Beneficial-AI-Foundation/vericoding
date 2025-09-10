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
lemma CountTransitionsHelperDefinition(s: string, pos: int, x: int, y: int, pred: int)
    requires 0 <= pos <= |s|
    requires forall i :: 0 <= i < |s| ==> s[i] == 'U' || s[i] == 'R'
    requires pred == -1 || pred == 0 || pred == 1
    decreases |s| - pos
    ensures CountTransitionsHelper(s, pos, x, y, pred) == 
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
{}
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
        result := 0;
        return;
    }
    
    var x := 0;
    var y := 0;
    var pred := -1;
    result := 0;
    var i := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant x >= 0
        invariant y >= 0
        invariant pred == -1 || pred == 0 || pred == 1
        invariant forall j :: 0 <= j < i ==> s[j] == 'U' || s[j] == 'R'
        invariant CountKingdomTransitions(s) == result + CountTransitionsHelper(s, i, x, y, pred)
        ensures CountKingdomTransitions(s) == old(result) + CountTransitionsHelper(s, i, old(x), old(y), old(pred))
    {
        var newX := if s[i] == 'U' then x else x + 1;
        var newY := if s[i] == 'U' then y + 1 else y;
        
        if newX == newY {
            x := newX;
            y := newY;
        } else {
            var cur := if newX > newY then 0 else 1;
            if pred != -1 && cur != pred {
                result := result + 1;
            }
            x := newX;
            y := newY;
            pred := cur;
        }
        i := i + 1;
    }
}
// </vc-code>

