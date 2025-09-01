

// <vc-helpers>
lemma min_int_seq(s: seq<int>, p: int->bool) returns (min_val: int, min_idx: int)
  requires exists i :: 0 <= i < |s| && p(s[i])
  ensures exists k :: 0 <= k < |s| && p(s[k]) && min_val == s[k] && min_idx == k
  ensures forall i :: 0 <= i < |s| && p(s[i]) ==> min_val <= s[i]
{
  var found_min := false;
  var current_min_val := 0;
  var current_min_idx := 0;

  for i := 0 to |s| - 1
    invariant 0 <= i <= |s|
    invariant !found_min || (exists k :: 0 <= k < i && p(s[k]) && current_min_val == s[k] && current_min_idx == k)
    invariant !found_min || (forall k :: 0 <= k < i && p(s[k]) ==> current_min_val <= s[k])
  {
    if p(s[i]) {
      if !found_min || s[i] < current_min_val {
        current_min_val := s[i];
        current_min_idx := i;
        found_min := true;
      }
    }
  }
  min_val := current_min_val;
  min_idx := current_min_idx;
}
// </vc-helpers>

// <vc-spec>
method PluckSmallestEven(nodes: seq<int>) returns (result: seq<int>)
  // pre-conditions-start
  requires |nodes| <= 10000
  requires forall i :: 0 <= i < |nodes| ==> nodes[i] >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures |result| == 0 || |result| == 2
  ensures |result| == 2 ==> 0 <= result[1] < |nodes| && nodes[result[1]] == result[0]
  ensures |result| == 2 ==> result[0] % 2 == 0
  ensures |result| == 2 ==> forall i :: 0 <= i < |nodes| && nodes[i] % 2 == 0 ==> result[0] <= nodes[i]
  ensures |result| == 2 ==> forall i :: 0 <= i < result[1] ==> nodes[i] % 2 != 0 || nodes[i] > result[0]
  ensures |result| == 0 ==> forall i :: 0 <= i < |nodes| ==> nodes[i] % 2 != 0
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var min_even_val := -1;
  var min_even_idx := -1;
  var found_even := false;

  for i := 0 to |nodes| - 1
    invariant 0 <= i <= |nodes|
    invariant !found_even || (exists k :: 0 <= k < i && nodes[k] % 2 == 0 && min_even_val == nodes[k] && min_even_idx == k)
    invariant !found_even || (forall k :: 0 <= k < i && nodes[k] % 2 == 0 ==> min_even_val <= nodes[k])
    invariant !found_even || min_even_val % 2 == 0
  {
    if nodes[i] % 2 == 0 {
      if !found_even || nodes[i] < min_even_val {
        min_even_val := nodes[i];
        min_even_idx := i;
        found_even := true;
      }
    }
  }

  if found_even {
    return [min_even_val, min_even_idx];
  } else {
    return [];
  }
}
// </vc-code>

