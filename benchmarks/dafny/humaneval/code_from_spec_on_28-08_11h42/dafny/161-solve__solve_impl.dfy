// <vc-helpers>
lemma ForallAlphaImpliesReverse(s: string, rev: string)
  requires forall i :: 0 <= i < |s| ==> !is_alpha(s[i])
  requires |rev| == |s|
  requires forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
  ensures forall i :: 0 <= i < |s| ==> s[i] == rev[|rev| - 1 - i]
{
}

lemma ExistsAlphaImpliesFlipCase(s: string, t: string)
  requires exists i :: 0 <= i < |s| && is_alpha(s[i])
  requires |s| == |t|
  requires forall i :: 0 <= i < |t| ==> if is_alpha(s[i]) then t[i] == flip_case(s[i]) else t[i] == s[i]
  ensures t == flip_case_string(s)
{
  FlipCaseStringEquiv(s, t);
}

lemma FlipCaseStringEquiv(s: string, t: string)
  requires |s| == |t|
  requires forall i :: 0 <= i < |t| ==> if is_alpha(s[i]) then t[i] == flip_case(s[i]) else t[i] == s[i]
  ensures t == flip_case_string(s)
{
  if |s| == 0 {
    assert t == "";
    assert flip_case_string(s) == "";
  } else {
    var rest_s := s[1..];
    var rest_t := t[1..];
    assert |rest_s| == |rest_t|;
    assert forall i :: 0 <= i < |rest_t| ==> if is_alpha(rest_s[i]) then rest_t[i] == flip_case(rest_s[i]) else rest_t[i] == rest_s[i];
    FlipCaseStringEquiv(rest_s, rest_t);
    assert rest_t == flip_case_string(rest_s);
    
    if is_alpha(s[0]) {
      assert t[0] == flip_case(s[0]);
      assert t == [flip_case(s[0])] + rest_t;
      assert flip_case_string(s) == [flip_case(s[0])] + flip_case_string(s[1..]);
    } else {
      assert t[0] == s[0];
      assert t == [s[0]] + rest_t;
      assert flip_case_string(s) == [s[0]] + flip_case_string(s[1..]);
    }
  }
}

function flip_case_string(s: string): string
{
  if |s| == 0 then ""
  else (if is_alpha(s[0]) then [flip_case(s[0])] else [s[0]]) + flip_case_string(s[1..])
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (t: string)
  // post-conditions-start 
  ensures |s| == |t|
  ensures (forall i :: 0 <= i < |s| ==> !is_alpha(s[i])) ==> (forall i :: 0 <= i < |s| ==> s[i] == t[|t| - 1 - i])
  ensures (exists i :: 0 <= i < |s| && is_alpha(s[i])) ==> 
    (forall i :: 0 <= i < |t| ==> if is_alpha(s[i]) then t[i] == flip_case(s[i]) else t[i] == s[i])
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var has_alpha := false;
  var i := 0;
  
  while i < |s|
    invariant 0 <= i <= |s|
    invariant has_alpha <==> exists j :: 0 <= j < i && is_alpha(s[j])
  {
    if is_alpha(s[i]) {
      has_alpha := true;
    }
    i := i + 1;
  }
  
  if has_alpha {
    t := "";
    i := 0;
    while i < |s|
      invariant 0 <= i <= |s|
      invariant |t| == i
      invariant forall j :: 0 <= j < i ==> if is_alpha(s[j]) then t[j] == flip_case(s[j]) else t[j] == s[j]
    {
      if is_alpha(s[i]) {
        t := t + [flip_case(s[i])];
      } else {
        t := t + [s[i]];
      }
      i := i + 1;
    }
    ExistsAlphaImpliesFlipCase(s, t);
  } else {
    var rev := reverse(s);
    t := rev;
    ForallAlphaImpliesReverse(s, rev);
  }
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