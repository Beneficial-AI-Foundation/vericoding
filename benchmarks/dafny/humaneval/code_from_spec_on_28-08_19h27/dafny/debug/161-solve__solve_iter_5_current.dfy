// <vc-helpers>
predicate case_flipped_at(s: string, t: string, i: int)
  requires 0 <= i < |s| == |t|
{
  if is_alpha(s[i]) then t[i] == flip_case(s[i]) else t[i] == s[i]
}

predicate all_case_flipped(s: string, t: string)
  requires |s| == |t|
{
  forall i :: 0 <= i < |s| ==> case_flipped_at(s, t, i)
}

predicate has_alpha_flipped(s: string, t: string)
  requires |s| == |t|
{
  (forall i :: 0 <= i < |s| ==> !is_alpha(s[i])) ||
  (exists i :: 0 <= i < |s| && is_alpha(s[i]) && t[i] == flip_case(s[i]))
}

predicate case_flipped_at_prefix(s: string, t: string, pos: int, len: int)
  requires 0 <= pos < len <= |s|
  requires len <= |t|
{
  if is_alpha(s[pos]) then t[pos] == flip_case(s[pos]) else t[pos] == s[pos]
}

predicate has_alpha_flipped_prefix(s: string, t: string, len: int)
  requires len <= |s| && len <= |t|
{
  (forall i :: 0 <= i < len ==> !is_alpha(s[i])) ||
  (exists i :: 0 <= i < len && is_alpha(s[i]) && t[i] == flip_case(s[i]))
}

lemma has_alpha_in_prefix(s: string, flipped: string, i: int, found_alpha: bool)
  requires 0 <= i < |s|
  requires |flipped| == i
  requires found_alpha ==> exists j :: 0 <= j < i && is_alpha(s[j])
  requires forall j :: 0 <= j < i ==> case_flipped_at_prefix(s, flipped, j, i)
  requires is_alpha(s[i])
  ensures has_alpha_flipped_prefix(s, flipped + [flip_case(s[i])], i + 1)
{
  var new_flipped := flipped + [flip_case(s[i])];
  assert |new_flipped| == i + 1;
  assert new_flipped[i] == flip_case(s[i]);
  assert is_alpha(s[i]) && new_flipped[i] == flip_case(s[i]);
}

lemma preserve_has_alpha(s: string, flipped: string, i: int, found_alpha: bool)
  requires 0 <= i < |s|
  requires |flipped| == i
  requires found_alpha ==> exists j :: 0 <= j < i && is_alpha(s[j])
  requires forall j :: 0 <= j < i ==> case_flipped_at_prefix(s, flipped, j, i)
  requires found_alpha ==> has_alpha_flipped_prefix(s, flipped, i)
  requires !is_alpha(s[i])
  ensures has_alpha_flipped_prefix(s, flipped + [s[i]], i + 1) == has_alpha_flipped_prefix(s, flipped, i)
{
}

lemma prefix_to_full_case_flipped(s: string, t: string)
  requires |s| == |t|
  requires forall j :: 0 <= j < |s| ==> case_flipped_at_prefix(s, t, j, |s|)
  ensures all_case_flipped(s, t)
{
  forall i | 0 <= i < |s|
    ensures case_flipped_at(s, t, i)
  {
    assert case_flipped_at_prefix(s, t, i, |s|);
  }
}

lemma prefix_to_full_has_alpha(s: string, t: string)
  requires |s| == |t|
  requires has_alpha_flipped_prefix(s, t, |s|)
  ensures has_alpha_flipped(s, t)
{
}

lemma maintain_case_flipped_invariant(s: string, flipped: string, i: int)
  requires 0 <= i < |s|
  requires |flipped| == i
  requires forall j :: 0 <= j < i ==> case_flipped_at_prefix(s, flipped, j, i)
  requires is_alpha(s[i])
  ensures forall j :: 0 <= j < i + 1 ==> case_flipped_at_prefix(s, flipped + [flip_case(s[i])], j, i + 1)
{
  var new_flipped := flipped + [flip_case(s[i])];
  forall j | 0 <= j < i + 1
    ensures case_flipped_at_prefix(s, new_flipped, j, i + 1)
  {
    if j < i {
      assert case_flipped_at_prefix(s, flipped, j, i);
      assert new_flipped[j] == flipped[j];
    } else {
      assert j == i;
      assert new_flipped[j] == flip_case(s[i]);
    }
  }
}

lemma maintain_case_flipped_invariant_non_alpha(s: string, flipped: string, i: int)
  requires 0 <= i < |s|
  requires |flipped| == i
  requires forall j :: 0 <= j < i ==> case_flipped_at_prefix(s, flipped, j, i)
  requires !is_alpha(s[i])
  ensures forall j :: 0 <= j < i + 1 ==> case_flipped_at_prefix(s, flipped + [s[i]], j, i + 1)
{
  var new_flipped := flipped + [s[i]];
  forall j | 0 <= j < i + 1
    ensures case_flipped_at_prefix(s, new_flipped, j, i + 1)
  {
    if j < i {
      assert case_flipped_at_prefix(s, flipped, j, i);
      assert new_flipped[j] == flipped[j];
    } else {
      assert j == i;
      assert new_flipped[j] == s[i];
      assert !is_alpha(s[i]);
    }
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method solve(s: string) returns (t: string)
Process input. Ensures: returns the correct size/count; the condition holds for all values; there exists a value satisfying the condition.
*/
// </vc-description>

// <vc-spec>
method solve(s: string) returns (t: string)
  ensures |t| == |s|
  ensures all_case_flipped(s, t)
  ensures has_alpha_flipped(s, t)
// </vc-spec>
// <vc-code>
{
  var flipped := "";
  var i := 0;
  var found_alpha := false;
  
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |flipped| == i
    invariant forall j :: 0 <= j < i ==> case_flipped_at_prefix(s, flipped, j, i)
    invariant found_alpha <==> exists j :: 0 <= j < i && is_alpha(s[j])
    invariant found_alpha ==> has_alpha_flipped_prefix(s, flipped, i)
  {
    if is_alpha(s[i]) {
      has_alpha_in_prefix(s, flipped, i, found_alpha);
      maintain_case_flipped_invariant(s, flipped, i);
      flipped := flipped + [flip_case(s[i])];
      found_alpha := true;
    } else {
      maintain_case_flipped_invariant_non_alpha(s, flipped, i);
      flipped := flipped + [s[i]];
      if found_alpha {
        preserve_has_alpha(s, flipped[..i], i, found_alpha);
      }
    }
    i := i + 1;
  }
  
  if !found_alpha {
    assert forall j :: 0 <= j < |s| ==> !is_alpha(s[j]);
  }
  
  t := flipped;
  prefix_to_full_case_flipped(s, t);
  prefix_to_full_has_alpha(s, t);
}
// </vc-code>

method reverse(s: string) returns (rev: string)
  // pre-conditions-start
  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
  // pre-conditions-end
{
  assume{:axiom} false;
}
function is_alpha(c: char) : bool {
  'a' <= c <= 'z' || 'A' <= c <= 'Z'
}
// pure-end
function flip_case(c: char): (flipped: char)
  requires is_alpha(c)
  ensures is_alpha(flipped)
{
  if 'a' <= c <= 'z' then c - 'a' + 'A' else c - 'A' + 'a'
}
// pure-end