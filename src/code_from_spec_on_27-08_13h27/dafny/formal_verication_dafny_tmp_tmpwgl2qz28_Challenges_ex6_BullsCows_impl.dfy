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
lemma BullSpecEquivalence(s: seq<nat>, u: seq<nat>)
  requires 0 <= |u| == |s| && nomultiples(u)
  ensures bullspec(s, u) == reccbull(s, u, 0)
{
}

lemma CowSpecEquivalence(s: seq<nat>, u: seq<nat>)
  requires 0 <= |u| == |s| && nomultiples(u)
  ensures cowspec(s, u) == recccow(s, u, 0)
{
}

lemma BullInvariant(s: seq<nat>, u: seq<nat>, i: int, b: nat)
  requires 0 <= i <= |s| == |u|
  requires nomultiples(u)
  requires b == reccbull(s, u, 0) - reccbull(s, u, i)
  ensures i == |s| ==> b == bullspec(s, u)
{
  if i == |s| {
    assert reccbull(s, u, i) == 0;
    assert b == reccbull(s, u, 0);
    BullSpecEquivalence(s, u);
    assert b == bullspec(s, u);
  }
}

lemma CowInvariant(s: seq<nat>, u: seq<nat>, i: int, c: nat)
  requires 0 <= i <= |s| == |u|
  requires nomultiples(u)
  requires c == recccow(s, u, 0) - recccow(s, u, i)
  ensures i == |s| ==> c == cowspec(s, u)
{
  if i == |s| {
    assert recccow(s, u, i) == 0;
    assert c == recccow(s, u, 0);
    CowSpecEquivalence(s, u);
    assert c == cowspec(s, u);
  }
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
method ComputeBullsCows(s: seq<nat>, u: seq<nat>) returns (b: nat, c: nat)
  requires 0 < |u| == |s| <= 10
  requires nomultiples(u) && nomultiples(s)
  ensures b >= 0 && c >= 0
  ensures b == bullspec(s, u)
  ensures c == cowspec(s, u)
{
  b := 0;
  c := 0;
  var i := 0;
  
  while i < |s|
    invariant 0 <= i <= |s|
    invariant b == reccbull(s, u, 0) - reccbull(s, u, i)
    invariant c == recccow(s, u, 0) - recccow(s, u, i)
  {
    if s[i] == u[i] {
      b := b + 1;
    } else if u[i] in s {
      c := c + 1;
    }
    i := i + 1;
  }
  
  BullInvariant(s, u, i, b);
  CowInvariant(s, u, i, c);
}
// </vc-code>
