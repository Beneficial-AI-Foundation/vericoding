//ATOM 
function bullspec(s:seq<nat>, u:seq<nat>): nat
requires 0 <= |u| == |s| && nomultiples(u)
{reccbull(s, u, 0)}

//ATOM 
function cowspec(s:seq<nat>, u:seq<nat>): nat
requires 0 <= |u| == |s| && nomultiples(u)
{recccow(s, u, 0)}

//ATOM 
function reccbull(s: seq<nat>, u:seq<nat>, i:int): nat
requires 0 <= i <= |s| == |u|
{
    if i ==|s| then 0
    else if s[i] == u[i] then reccbull(s, u, i + 1) + 1
    else reccbull(s, u, i + 1)
}

//ATOM 
function recccow(s: seq<nat>, u:seq<nat>, i:int): nat
requires 0 <= i <= |s| == |u|
{
    if i == |s| then 0
    else if s[i] != u[i] && u[i] in s then recccow(s, u, i + 1) + 1
    else recccow(s, u, i + 1)
}

//ATOM 
predicate nomultiples(u:seq<nat>) 
{forall j, k :: 0<=j<k<|u| ==> u[j] != u[k]}

/* code modified by LLM (iteration 2): added helper function to count bulls up to index i */
function countBulls(s: seq<nat>, u: seq<nat>, i: int): nat
requires 0 <= i <= |s| == |u|
{
    if i == 0 then 0
    else countBulls(s, u, i-1) + (if s[i-1] == u[i-1] then 1 else 0)
}

/* code modified by LLM (iteration 2): added helper function to count cows up to index i */
function countCows(s: seq<nat>, u: seq<nat>, i: int): nat
requires 0 <= i <= |s| == |u|
{
    if i == 0 then 0
    else countCows(s, u, i-1) + (if s[i-1] != u[i-1] && u[i-1] in s then 1 else 0)
}

/* code modified by LLM (iteration 2): lemma to prove relationship between recursive and iterative bull counting */
lemma BullsRelation(s: seq<nat>, u: seq<nat>, i: int)
requires 0 <= i <= |s| == |u|
ensures reccbull(s, u, 0) == countBulls(s, u, i) + reccbull(s, u, i)
{
    if i == 0 {
        assert countBulls(s, u, 0) == 0;
    } else {
        BullsRelation(s, u, i-1);
        assert reccbull(s, u, 0) == countBulls(s, u, i-1) + reccbull(s, u, i-1);
        if s[i-1] == u[i-1] {
            assert reccbull(s, u, i-1) == reccbull(s, u, i) + 1;
        } else {
            assert reccbull(s, u, i-1) == reccbull(s, u, i);
        }
    }
}

/* code modified by LLM (iteration 2): lemma to prove relationship between recursive and iterative cow counting */
lemma CowsRelation(s: seq<nat>, u: seq<nat>, i: int)
requires 0 <= i <= |s| == |u|
ensures recccow(s, u, 0) == countCows(s, u, i) + recccow(s, u, i)
{
    if i == 0 {
        assert countCows(s, u, 0) == 0;
    } else {
        CowsRelation(s, u, i-1);
        assert recccow(s, u, 0) == countCows(s, u, i-1) + recccow(s, u, i-1);
        if s[i-1] != u[i-1] && u[i-1] in s {
            assert recccow(s, u, i-1) == recccow(s, u, i) + 1;
        } else {
            assert recccow(s, u, i-1) == recccow(s, u, i);
        }
    }
}

//IMPL BullsCows
method BullsCows (s:seq<nat>, u:seq<nat>) returns (b:nat, c:nat) 
requires 0 < |u| == |s| <= 10
requires nomultiples(u) && nomultiples(s);
ensures b >= 0 && c >= 0
ensures b == bullspec(s, u)
ensures c == cowspec(s, u)
{
    b := 0;
    c := 0;
    
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        /* code modified by LLM (iteration 2): corrected invariants using helper functions and lemmas */
        invariant b == countBulls(s, u, i)
        invariant c == countCows(s, u, i)
    {
        if s[i] == u[i] {
            b := b + 1;
        } else if u[i] in s {
            /* code modified by LLM (iteration 2): fixed cow logic to check if u[i] is in s (matching the recursive definition) */
            c := c + 1;
        }
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 2): added assertions to connect loop results with specifications */
    BullsRelation(s, u, |s|);
    CowsRelation(s, u, |s|);
    assert b == countBulls(s, u, |s|);
    assert c == countCows(s, u, |s|);
    assert reccbull(s, u, |s|) == 0;
    assert recccow(s, u, |s|) == 0;
}