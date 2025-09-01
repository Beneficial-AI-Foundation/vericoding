method solve(s: string) returns (t: string)
  // post-conditions-start 
  ensures |s| == |t|
  ensures (forall i :: 0 <= i < |s| ==> !is_alpha(s[i])) ==> (forall i :: 0 <= i < |s| ==> s[i] == t[|t| - 1 - i])
  ensures (exists i :: 0 <= i < |s| && is_alpha(s[i])) ==> 
    (forall i :: 0 <= i < |t| ==> if is_alpha(s[i]) then t[i] == flip_case(s[i]) else t[i] == s[i])
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma reverse_lemma(s: string, t: string, rev: string)
  requires |rev| == |s|
  requires forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
  requires |s| == |t|
  requires forall i :: 0 <= i < |s| ==> !is_alpha(s[i])
  ensures forall i :: 0 <= i < |s| ==> s[i] == t[|t| - 1 - i]
{
  forall i | 0 <= i < |s|
    ensures s[i] == t[|t| - 1 - i]
  {
    assert t == rev;
    assert t[|t| - 1 - i] == rev[|rev| - 1 - i];
    assert rev[|rev| - 1 - i] == s[i];
  }
}

lemma flip_case_lemma(s: string, t: string)
  requires |s| == |t|
  requires forall i :: 0 <= i < |t| ==> if is_alpha(s[i]) then t[i] == flip_case(s[i]) else t[i] == s[i]
  ensures (exists i :: 0 <= i < |s| && is_alpha(s[i])) ==> 
    (forall i :: 0 <= i < |t| ==> if is_alpha(s[i]) then t[i] == flip_case(s[i]) else t[i] == s[i])
{
}
// </vc-helpers>

// <vc-spec>
method reverse(s: string) returns (rev: string)
  // pre-conditions-start
  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
  // pre-conditions-end
// </vc-spec>
// <vc-code>
{
  var rev_str := reverse(s);
  var has_alpha := false;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant !has_alpha ==> forall j :: 0 <= j < i ==> !is_alpha(s[j])
    invariant has_alpha ==> exists j :: 0 <= j < i && is_alpha(s[j])
  {
    if is_alpha(s[i]) {
      has_alpha := true;
    }
    i := i + 1;
  }
  
  if has_alpha {
    var t_arr := new char[|s|];
    i := 0;
    while i < |s|
      invariant 0 <= i <= |s|
      invariant forall j :: 0 <= j < i ==> if is_alpha(s[j]) then t_arr[j] == flip_case(s[j]) else t_arr[j] == s[j]
    {
      if is_alpha(s[i]) {
        t_arr[i] := flip_case(s[i]);
      } else {
        t_arr[i] := s[i];
      }
      i := i + 1;
    }
    t := new string(t_arr);
  } else {
    t := rev_str;
  }
}
// </vc-code>

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