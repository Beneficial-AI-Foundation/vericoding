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
lemma ReccBull_step(s: seq<nat>, u: seq<nat>, i: int)
  requires 0 <= i < |s|
  requires |s| == |u|
  ensures reccbull(s, u, i) == (if s[i] == u[i] then reccbull(s, u, i + 1) + 1 else reccbull(s, u, i + 1))
{
  assert reccbull(s, u, i) ==
    if i == |s| then 0 else if s[i] == u[i] then reccbull(s, u, i + 1) + 1 else reccbull(s, u, i + 1);
  assert i != |s|;
  assert (if i == |s| then 0 else if s[i] == u[i] then reccbull(s, u, i + 1) + 1 else reccbull(s, u, i + 1))
    == (if s[i] == u[i] then reccbull(s, u, i + 1) + 1 else reccbull(s, u, i + 1));
}

lemma ReccCow_step(s: seq<nat>, u: seq<nat>, i: int)
  requires 0 <= i < |s|
  requires |s| == |u|
  ensures recccow(s, u, i) == (if s[i] != u[i] && u[i] in s then recccow(s, u, i + 1) + 1 else recccow(s, u, i + 1))
{
  assert recccow(s, u, i) ==
    if i == |s| then 0 else if s[i] != u[i] && u[i] in s then recccow(s, u, i + 1) + 1 else recccow(s, u, i + 1);
  assert i != |s|;
  assert (if i == |s| then 0 else if s[i] != u[i] && u[i] in s then recccow(s, u, i + 1) + 1 else recccow(s, u, i + 1))
    == (if s[i] != u[i] && u[i] in s then recccow(s, u, i + 1) + 1 else recccow(s, u, i + 1));
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
  var n := |s|;
  b := 0;
  c := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant b + reccbull(s, u, i) == reccbull(s, u, 0)
    invariant c + recccow(s, u, i) == recccow(s, u, 0)
    decreases n - i
  {
    if s[i] == u[i] {
      ReccBull_step(s, u, i);
      // From the lemma and the branch condition we get the one-step relation
      assert reccbull(s, u, i) == reccbull(s, u, i + 1) + 1;
      b := b + 1;
    } else if u[i] in s {
      // In this branch we know s[i] != u[i] and u[i] in s
      ReccCow_step(s, u, i);
      assert s[i] != u[i] && u[i] in s;
      assert recccow(s, u, i) == recccow(s, u, i + 1) + 1;
      c := c + 1;
    }
    i := i + 1;
  }
}
// </vc-code>

