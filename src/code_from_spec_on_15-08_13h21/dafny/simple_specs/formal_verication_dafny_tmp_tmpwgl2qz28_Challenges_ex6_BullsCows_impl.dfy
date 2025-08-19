//ATOM
/* code modified by LLM (iteration 1): added decreases clause to fix termination */
function reccbull(s: seq<nat>, u:seq<nat>, i:int): nat
requires 0 <= i <= |s| == |u|
decreases |s| - i
{
  if i ==|s| then 0
  else if s[i] == u[i] then reccbull(s, u, i + 1) + 1
  else reccbull(s, u, i + 1)
}


//ATOM
// see pdf 'ex6 & 7 documentation' for excercise question

function bullspec(s:seq<nat>, u:seq<nat>): nat
requires 0 <= |u| == |s| && nomultiples(u)
{reccbull(s, u, 0)}


//ATOM
/* code modified by LLM (iteration 1): added decreases clause to fix termination */
function recccow(s: seq<nat>, u:seq<nat>, i:int): nat
requires 0 <= i <= |s| == |u|
decreases |s| - i
{
  if i == |s| then 0
  else if s[i] != u[i] && u[i] in s then recccow(s, u, i + 1) + 1
  else recccow(s, u, i + 1)
}


//ATOM

function cowspec(s:seq<nat>, u:seq<nat>): nat
requires 0 <= |u| == |s| && nomultiples(u)
{recccow(s, u, 0)}


//ATOM

predicate nomultiples(u:seq<nat>) 
{forall j, k :: 0<=j<k<|u| ==> u[j] != u[k]}


//IMPL BullsCows

method BullsCows (s:seq<nat>, u:seq<nat>) returns (b:nat, c:nat) 
requires 0 < |u| == |s| <= 10
requires nomultiples(u) && nomultiples(s)
ensures b >= 0 && c >= 0
ensures b == bullspec(s, u)
ensures c == cowspec(s, u)
{
    b := bullspec(s, u);
    c := cowspec(s, u);
}