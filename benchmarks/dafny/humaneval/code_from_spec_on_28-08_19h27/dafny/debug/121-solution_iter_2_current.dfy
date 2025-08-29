// <vc-helpers>
lemma sum_append(s1: seq<int>, s2: seq<int>, p1: seq<bool>, p2: seq<bool>)
  requires |s1| == |p1| && |s2| == |p2|
  ensures sum(s1 + s2, p1 + p2) == sum(s1, p1) + sum(s2, p2)
{
  if |s1| == 0 {
    assert s1 + s2 == s2;
    assert p1 + p2 == p2;
  } else {
    assert (s1 + s2)[1..] == s1[1..] + s2;
    assert (p1 + p2)[1..] == p1[1..] + p2;
    sum_append(s1[1..], s2, p1[1..], p2);
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def solution(lst: List[int]) -> int
Given a non-empty list of integers, return the sum of all of the odd elements that are in even positions.
*/
// </vc-description>

// <vc-spec>
method solution(lst: seq<int>) returns (result: int)
  requires |lst| > 0
  ensures result == sum(lst, seq(|lst|, i => i % 2 == 0 && i < |lst| && lst[i] % 2 == 1))
// </vc-spec>
// <vc-code>
{
  result := 0;
  var i := 0;
  while i < |lst|
    invariant 0 <= i <= |lst|
    invariant result == sum(lst[..i], seq(i, j => j % 2 == 0 && j < |lst| && lst[j] % 2 == 1))
  {
    if i % 2 == 0 && lst[i] % 2 == 1 {
      result := result + lst[i];
    }
    
    var old_result := result;
    var old_i := i;
    i := i + 1;
    
    // Prove the invariant is maintained
    var s_old := lst[..old_i];
    var p_old := seq(old_i, j => j % 2 == 0 && j < |lst| && lst[j] % 2 == 1);
    var s_new := lst[..i];
    var p_new := seq(i, j => j % 2 == 0 && j < |lst| && lst[j] % 2 == 1);
    
    assert s_new == s_old + [lst[old_i]];
    assert p_new == p_old + [old_i % 2 == 0 && old_i < |lst| && lst[old_i] % 2 == 1];
    
    sum_append(s_old, [lst[old_i]], p_old, [old_i % 2 == 0 && old_i < |lst| && lst[old_i] % 2 == 1]);
  }
  
  // Prove postcondition
  assert lst[..|lst|] == lst;
  assert seq(|lst|, j => j % 2 == 0 && j < |lst| && lst[j] % 2 == 1) == seq(|lst|, i => i % 2 == 0 && i < |lst| && lst[i] % 2 == 1);
}
// </vc-code>

function sum(s: seq<int>, p: seq<bool>) : int
  requires |s| == |p|
{
  if |s| == 0 then 0 else (if p[0] then s[0] else 0) + sum(s[1..], p[1..])
}
// pure-end