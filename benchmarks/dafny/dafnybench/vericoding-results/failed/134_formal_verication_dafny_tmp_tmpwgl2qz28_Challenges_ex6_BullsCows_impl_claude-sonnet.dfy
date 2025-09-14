// see pdf 'ex6 & 7 documentation' for excercise question

function bullspec(s:seq<nat>, u:seq<nat>): nat
requires 0 <= |u| == |s| && nomultiples(u)
{reccbull(s, u, 0)}

function cowspec(s:seq<nat>, u:seq<nat>): nat
requires 0 <= |u| == |s| && nomultiples(u)
{recccow(s, u, 0)}

function reccbull(s: seq<nat>, u:seq<nat>, i:int): nat
requires 0 <= i <= |s| == |u|
decreases |s| - i
{
    if i ==|s| then 0
    else if s[i] == u[i] then reccbull(s, u, i + 1) + 1
    else reccbull(s, u, i + 1)
}

function recccow(s: seq<nat>, u:seq<nat>, i:int): nat
requires 0 <= i <= |s| == |u|
decreases |s| - i
{
    if i == |s| then 0
    else if s[i] != u[i] && u[i] in s then recccow(s, u, i + 1) + 1
    else recccow(s, u, i + 1)
}

predicate nomultiples(u:seq<nat>) 
{forall j, k :: 0<=j<k<|u| ==> u[j] != u[k]}

// <vc-helpers>
lemma BullsLemma(s: seq<nat>, u: seq<nat>, i: int)
    requires 0 <= i <= |s| == |u|
    ensures reccbull(s, u, 0) - reccbull(s, u, i) == reccbull(s, u, 0) - reccbull(s, u, i)
{
}

lemma CowsLemma(s: seq<nat>, u: seq<nat>, i: int)
    requires 0 <= i <= |s| == |u|
    ensures recccow(s, u, 0) - recccow(s, u, i) >= 0
    decreases |s| - i
{
    if i == |s| {
        assert recccow(s, u, i) == 0;
        CowsNonNegative(s, u, 0);
    } else {
        CowsLemma(s, u, i + 1);
        assert recccow(s, u, 0) - recccow(s, u, i + 1) >= 0;
        if s[i] != u[i] && u[i] in s {
            assert recccow(s, u, i) == recccow(s, u, i + 1) + 1;
            assert recccow(s, u, 0) - recccow(s, u, i) == recccow(s, u, 0) - recccow(s, u, i + 1) - 1;
        } else {
            assert recccow(s, u, i) == recccow(s, u, i + 1);
            assert recccow(s, u, 0) - recccow(s, u, i) == recccow(s, u, 0) - recccow(s, u, i + 1);
        }
    }
}

lemma CowsNonNegative(s: seq<nat>, u: seq<nat>, i: int)
    requires 0 <= i <= |s| == |u|
    ensures recccow(s, u, i) >= 0
    decreases |s| - i
{
    if i == |s| {
        assert recccow(s, u, i) == 0;
    } else {
        CowsNonNegative(s, u, i + 1);
    }
}

lemma BullsInvariantLemma(s: seq<nat>, u: seq<nat>, i: int)
    requires 0 <= i < |s| == |u|
    ensures (if s[i] == u[i] then 1 else 0) == reccbull(s, u, i) - reccbull(s, u, i + 1)
{
}

lemma CowsInvariantLemma(s: seq<nat>, u: seq<nat>, i: int)
    requires 0 <= i < |s| == |u|
    ensures (if s[i] != u[i] && u[i] in s then 1 else 0) == recccow(s, u, i) - recccow(s, u, i + 1)
{
}

lemma CowsPreservesInvariant(s: seq<nat>, u: seq<nat>, i: int)
    requires 0 <= i < |s| == |u|
    requires recccow(s, u, 0) - recccow(s, u, i) >= 0
    ensures recccow(s, u, 0) - recccow(s, u, i + 1) >= 0
{
    CowsLemma(s, u, i + 1);
}
// </vc-helpers>

// <vc-spec>
method BullsCows (s:seq<nat>, u:seq<nat>) returns (b:nat, c:nat) 
requires 0 < |u| == |s| <= 10
requires nomultiples(u) && nomultiples(s);
ensures b >= 0 && c >= 0
ensures b == bullspec(s, u)
ensures c == cowspec(s, u)
// </vc-spec>
// <vc-code>
{
    b := 0;
    c := 0;
    var i := 0;
    
    CowsLemma(s, u, 0);
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant b == reccbull(s, u, 0) - reccbull(s, u, i)
        invariant c == recccow(s, u, 0) - recccow(s, u, i)
        invariant recccow(s, u, 0) - recccow(s, u, i) >= 0
    {
        CowsPreservesInvariant(s, u, i);
        if s[i] == u[i] {
            BullsInvariantLemma(s, u, i);
            b := b + 1;
        } else if u[i] in s {
            CowsInvariantLemma(s, u, i);
            c := c + 1;
        } else {
            BullsInvariantLemma(s, u, i);
            CowsInvariantLemma(s, u, i);
        }
        i := i + 1;
    }
}
// </vc-code>

