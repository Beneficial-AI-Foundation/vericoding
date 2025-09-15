// <vc-preamble>
function is_alpha(c: char) : bool {
  'a' <= c <= 'z' || 'A' <= c <= 'Z'
}
function flip_case(c: char): (flipped: char)
  requires is_alpha(c)
  ensures is_alpha(flipped)
{
  if 'a' <= c <= 'z' then c - 'a' + 'A' else c - 'A' + 'a'
}
// </vc-preamble>

// <vc-helpers>
function has_alpha(s: string): bool {
  exists i :: 0 <= i < |s| && is_alpha(s[i])
}

function reverse_string(s: string): string {
  if |s| == 0 then s else reverse_string(s[1..]) + [s[0]]
}

function flip_case_string(s: string): string {
  if |s| == 0 then s else [if is_alpha(s[0]) then flip_case(s[0]) else s[0]] + flip_case_string(s[1..])
}

/* helper modified by LLM (iteration 2): added lemmas to prove reverse and flip properties */
lemma reverse_string_length(s: string)
  ensures |reverse_string(s)| == |s|
{
  if |s| == 0 {
  } else {
    reverse_string_length(s[1..]);
  }
}

lemma flip_case_string_length(s: string)
  ensures |flip_case_string(s)| == |s|
{
  if |s| == 0 {
  } else {
    flip_case_string_length(s[1..]);
  }
}

lemma reverse_string_property(s: string)
  ensures |reverse_string(s)| == |s|
  ensures forall i :: 0 <= i < |s| ==> reverse_string(s)[i] == s[|s| - 1 - i]
{
  if |s| == 0 {
  } else {
    reverse_string_length(s[1..]);
    reverse_string_property(s[1..]);
  }
}

lemma flip_case_string_property(s: string)
  ensures |flip_case_string(s)| == |s|
  ensures forall i :: 0 <= i < |s| ==> flip_case_string(s)[i] == (if is_alpha(s[i]) then flip_case(s[i]) else s[i])
{
  if |s| == 0 {
  } else {
    flip_case_string_property(s[1..]);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (t: string)

  ensures |s| == |t|
  ensures (forall i :: 0 <= i < |s| ==> !is_alpha(s[i])) ==> (forall i :: 0 <= i < |s| ==> s[i] == t[|t| - 1 - i])
  ensures (exists i :: 0 <= i < |s| && is_alpha(s[i])) ==> 
    (forall i :: 0 <= i < |t| ==> if is_alpha(s[i]) then t[i] == flip_case(s[i]) else t[i] == s[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): added lemma calls to establish postconditions */
  if has_alpha(s) {
    t := flip_case_string(s);
    flip_case_string_property(s);
  } else {
    t := reverse_string(s);
    reverse_string_property(s);
  }
}
// </vc-code>
