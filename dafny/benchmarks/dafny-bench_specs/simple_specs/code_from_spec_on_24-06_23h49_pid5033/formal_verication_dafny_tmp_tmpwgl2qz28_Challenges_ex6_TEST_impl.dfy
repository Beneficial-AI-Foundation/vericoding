//ATOM

function reccbull(s: seq<nat>, u:seq<nat>, i:int): nat
requires 0 <= i <= |s| == |u|
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

function recccow(s: seq<nat>, u:seq<nat>, i:int): nat
requires 0 <= i <= |s| == |u|
{
  if i == |s| then 0
  else if s[i] != u[i] && u[i] in s then recccow(s, u, i + 1) + 1
  else recccow(s, u, i + 1)
}


//ATOM

method BullsCows (s:seq<nat>, u:seq<nat>) returns (b:nat, c:nat) 
requires 0 < |u| == |s| <= 10
requires nomultiples(u) && nomultiples(s)
ensures b >= 0 && c >= 0
ensures b == bullspec(s, u)
ensures c == cowspec(s, u)
{
  /* code modified by LLM (iteration 1): Fixed implementation with correct loop invariants */
  b := 0;
  c := 0;
  
  // Calculate bulls by iterating through positions
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant b + reccbull(s, u, i) == reccbull(s, u, 0)
  {
    if s[i] == u[i] {
      b := b + 1;
    }
    i := i + 1;
  }
  
  // Calculate cows by iterating through positions
  i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant c + recccow(s, u, i) == recccow(s, u, 0)
  {
    if s[i] != u[i] && u[i] in s {
      c := c + 1;
    }
    i := i + 1;
  }
}


//ATOM

function cowspec(s:seq<nat>, u:seq<nat>): nat
requires 0 <= |u| == |s| && nomultiples(u)
{recccow(s, u, 0)}


//ATOM

predicate nomultiples(u:seq<nat>) 
{forall j, k :: 0<=j<k<|u| ==> u[j] != u[k]}


//IMPL 

method TEST(){
  /* code modified by LLM (iteration 1): Fixed test with sequences that satisfy nomultiples predicate */
  var s := [1, 2, 3, 4];
  var u := [5, 6, 7, 8];
  var b, c := BullsCows(s, u);
  print "Bulls: ", b, ", Cows: ", c, "\n";
}