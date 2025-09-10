predicate ValidInput(n: int, a: seq<int>)
{
    n >= 1 && |a| == n && forall i :: 0 <= i < n ==> a[i] >= 0
}

function CountSurvivors(n: int, a: seq<int>): int
    requires ValidInput(n, a)
{
    CountSurvivorsFrom(n, a, 0, n)
}

function CountSurvivorsFrom(n: int, a: seq<int>, start: int, left: int): int
    requires ValidInput(n, a)
    requires 0 <= start <= n
    requires left <= n
    decreases n - start
{
    if start >= n then 0
    else
        var i := n - 1 - start;
        var survives := if i < left then 1 else 0;
        var newLeft := if i - a[i] < left then i - a[i] else left;
        survives + CountSurvivorsFrom(n, a, start + 1, newLeft)
}

// <vc-helpers>
lemma CountSurvivorsFromCorrectness(n: int, a: seq<int>, start: int, left: int, survivors: int, currentLeft: int)
    requires ValidInput(n, a)
    requires 0 <= start <= n
    requires left <= n
    requires survivors >= 0
    requires currentLeft <= n
    ensures CountSurvivorsFrom(n, a, start, left) >= 0
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, a)
    ensures result >= 0
    ensures result <= n
    ensures result == CountSurvivors(n, a)
// </vc-spec>
// <vc-code>
{
    var survivors := 0;
    var currentLeft := n;
    var s := 0;
    
    while s < n
        invariant 0 <= s <= n
        invariant survivors >= 0
        invariant currentLeft <= n
        invariant survivors == CountSurvivorsFrom(n, a, 0, n) - CountSurvivorsFrom(n, a, s, currentLeft)
    {
        var i := n - 1 - s;
        
        if i < currentLeft {
            survivors := survivors + 1;
        }
        
        var newLeft := i - a[i];
        if newLeft < currentLeft {
            currentLeft := newLeft;
        }
        
        s := s + 1;
    }
    
    result := survivors;
}
// </vc-code>

