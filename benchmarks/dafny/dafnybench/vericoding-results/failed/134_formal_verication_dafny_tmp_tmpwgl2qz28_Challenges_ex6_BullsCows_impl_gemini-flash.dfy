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
function countOccurrences(s: seq<nat>, value: nat, start: int): nat
requires 0 <= start <= |s|
decreases |s| - start
{
  if start == |s| then 0
  else (if s[start] == value then 1 else 0) + countOccurrences(s, value, start + 1)
}

predicate NoMultiplesInRange(s: seq<nat>, start: int, end: int)
requires 0 <= start <= end <= |s|
{
    forall j, k :: start <= j < k < end ==> s[j] != s[k]
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
  var b_count: nat := 0;
  var c_count: nat := 0;

  for i := 0 to |s| - 1
    invariant 0 <= i <= |s|
    invariant b_count == reccbull(s, u, 0) - reccbull(s, u, i)
    invariant c_count == (recccow(s, u, 0) - recccow(s, u, i))
    invariant (forall j :: 0 <= j < i ==> 
        (s[j] == u[j] ==> b_count == (old(b_count) + 1)) &&
        (s[j] != u[j] && (exists k' :: 0 <= k' < |u| && u[k'] == s[j] && s[k'] != u[k']) ==> c_count == (old(c_count) + 1)) &&
        (s[j] != u[j] && !(exists k' :: 0 <= k' < |u| && u[k'] == s[j] && s[k'] != u[k']) ==> c_count == old(c_count))
    )
  {
    if s[i] == u[i] {
      b_count := b_count + 1;
    } else {
      var found: bool := false;
      for k := 0 to |u| - 1
        invariant 0 <= k <= |u|
        invariant !(found) ==> (forall l :: 0 <= l < k ==> u[l] != s[i]);
        invariant found ==> (exists l :: 0 <= l < k && u[l] == s[i] && s[l] != u[l])
      {
        if u[k] == s[i] {
          if s[k] != u[k] {
            found := true;
          }
        }
      }
      if found {
        c_count := c_count + 1;
      }
    }
  }

  return b_count, c_count;
}
// </vc-code>

