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
    ensures CountBulls(s, u, i) == 0
    decreases |s| - i
{
    if i == |s| {
    } else if s[i] == u[i] {
        BullsLemma(s, u, i + 1);
    } else {
        BullsLemma(s, u, i + 1);
    }
}

lemma CowsLemma(s: seq<nat>, u: seq<nat>, i: int)
    requires 0 <= i <= |s| == |u|
    ensures CountCows(s, u, i) == 0
    decreases |s| - i
{
    if i == |s| {
    } else if s[i] != u[i] && u[i] in s {
        CowsLemma(s, u, i + 1);
    } else {
        CowsLemma(s, u, i + 1);
    }
}

function CountBulls(s: seq<nat>, u: seq<nat>, i: int): nat
    requires 0 <= i <= |s| == |u|
    decreases |s| - i
{
    if i == |s| then 0
    else (if s[i] == u[i] then 1 else 0) + CountBulls(s, u, i + 1)
}

function CountCows(s: seq<nat>, u: seq<nat>, i: int): nat
    requires 0 <= i <= |s| == |u|
    decreases |s| - i
{
    if i == |s| then 0
    else (if s[i] != u[i] && u[i] in s then 1 else 0) + CountCows(s, u, i + 1)
}

lemma BullsEquiv(s: seq<nat>, u: seq<nat>, i: int)
    requires 0 <= i <= |s| == |u|
    ensures reccbull(s, u, i) == CountBulls(s, u, i)
    decreases |s| - i
{
    if i == |s| {
    } else {
        BullsEquiv(s, u, i + 1);
    }
}

lemma CowsEquiv(s: seq<nat>, u: seq<nat>, i: int)
    requires 0 <= i <= |s| == |u|
    ensures recccow(s, u, i) == CountCows(s, u, i)
    decreases |s| - i
{
    if i == |s| {
    } else {
        CowsEquiv(s, u, i + 1);
    }
}

lemma CountBullsDecomposition(s: seq<nat>, u: seq<nat>, i: int)
    requires 0 <= i < |s| == |u|
    ensures CountBulls(s, u, 0) == CountBulls(s, u, 0) - CountBulls(s, u, i) + (if s[i] == u[i] then 1 else 0) + CountBulls(s, u, i + 1)
{
    if i == 0 {
        assert CountBulls(s, u, 0) == (if s[0] == u[0] then 1 else 0) + CountBulls(s, u, 1);
    } else {
        assert CountBulls(s, u, i) == (if s[i] == u[i] then 1 else 0) + CountBulls(s, u, i + 1);
    }
}

lemma CountCowsDecomposition(s: seq<nat>, u: seq<nat>, i: int)
    requires 0 <= i < |s| == |u|
    ensures CountCows(s, u, 0) == CountCows(s, u, 0) - CountCows(s, u, i) + (if s[i] != u[i] && u[i] in s then 1 else 0) + CountCows(s, u, i + 1)
{
    if i == 0 {
        assert CountCows(s, u, 0) == (if s[0] != u[0] && u[0] in s then 1 else 0) + CountCows(s, u, 1);
    } else {
        assert CountCows(s, u, i) == (if s[i] != u[i] && u[i] in s then 1 else 0) + CountCows(s, u, i + 1);
    }
}

lemma InvariantMaintenance(s: seq<nat>, u: seq<nat>, i: int, b: nat, c: nat)
    requires 0 <= i < |s| == |u|
    requires b == CountBulls(s, u, 0) - CountBulls(s, u, i)
    requires c == CountCows(s, u, 0) - CountCows(s, u, i)
    ensures s[i] == u[i] ==> b + 1 == CountBulls(s, u, 0) - CountBulls(s, u, i + 1)
    ensures s[i] != u[i] && u[i] in s ==> c + 1 == CountCows(s, u, 0) - CountCows(s, u, i + 1)
    ensures s[i] != u[i] ==> b == CountBulls(s, u, 0) - CountBulls(s, u, i + 1)
    ensures (s[i] == u[i] || !(u[i] in s)) ==> c == CountCows(s, u, 0) - CountCows(s, u, i + 1)
{
    assert CountBulls(s, u, i) == (if s[i] == u[i] then 1 else 0) + CountBulls(s, u, i + 1);
    assert CountCows(s, u, i) == (if s[i] != u[i] && u[i] in s then 1 else 0) + CountCows(s, u, i + 1);
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method BullsCows (s:seq<nat>, u:seq<nat>) returns (b:nat, c:nat) 
requires 0 < |u| == |s| <= 10
requires nomultiples(u) && nomultiples(s);
ensures b >= 0 && c >= 0
ensures b == bullspec(s, u)
ensures c == cowspec(s, u)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    b := 0;
    c := 0;
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant b == CountBulls(s, u, 0) - CountBulls(s, u, i)
        invariant c == CountCows(s, u, 0) - CountCows(s, u, i)
        decreases |s| - i
    {
        InvariantMaintenance(s, u, i, b, c);
        if s[i] == u[i] {
            b := b + 1;
        } else if u[i] in s {
            c := c + 1;
        }
        i := i + 1;
    }
    
    assert CountBulls(s, u, |s|) == 0;
    assert CountCows(s, u, |s|) == 0;
    assert b == CountBulls(s, u, 0);
    assert c == CountCows(s, u, 0);
    
    BullsEquiv(s, u, 0);
    CowsEquiv(s, u, 0);
}
// </vc-code>
