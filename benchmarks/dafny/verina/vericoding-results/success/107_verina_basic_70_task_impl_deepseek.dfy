// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function FindFirstIndex(s: seq<int>, p: int -> bool, i: int): nat
  requires 0 <= i <= |s|
  requires exists j :: i <= j < |s| && p(s[j])
  ensures i <= FindFirstIndex(s, p, i) < |s|
  ensures p(s[FindFirstIndex(s, p, i)])
  ensures forall k :: i <= k < FindFirstIndex(s, p, i) ==> !p(s[k])
  decreases |s| - i
{
  if p(s[i]) then
    i
  else
    FindFirstIndex(s, p, i + 1)
}
// </vc-helpers>

// <vc-spec>
method LinearSearch3(a: seq<int>, p: int -> bool) returns (result: nat)
    requires 
        exists i :: 0 <= i < |a| && p(a[i])
    ensures 
        result < |a| &&
        p(a[result]) &&
        forall k :: 0 <= k < result ==> !p(a[k])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): verified implementation */
  result := FindFirstIndex(a, p, 0);
}
// </vc-code>
