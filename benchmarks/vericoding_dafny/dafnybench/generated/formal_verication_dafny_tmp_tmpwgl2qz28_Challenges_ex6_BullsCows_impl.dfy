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
lemma BullsLemma(s: seq<nat>, u: seq<nat>, i: int, bulls: nat)
requires 0 <= i <= |s| == |u|
requires bulls == reccbull(s, u, 0) - reccbull(s, u, i)
ensures bulls + reccbull(s, u, i) == reccbull(s, u, 0)
{
}

lemma CowsLemma(s: seq<nat>, u: seq<nat>, i: int, cows: nat)
requires 0 <= i <= |s| == |u|
requires cows == recccow(s, u, 0) - recccow(s, u, i)
ensures cows + recccow(s, u, i) == recccow(s, u, 0)
{
}
// </vc-helpers>

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
  
  assert i == |s|;
  assert reccbull(s, u, i) == 0;
  assert recccow(s, u, i) == 0;
  assert b == reccbull(s, u, 0);
  assert c == recccow(s, u, 0);
}
// </vc-code>