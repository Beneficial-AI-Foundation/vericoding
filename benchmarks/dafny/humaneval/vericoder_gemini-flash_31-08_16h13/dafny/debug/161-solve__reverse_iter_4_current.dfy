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
function reverse_string(s: string): (rev: string)
  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
{
  var n := |s];
  if n == 0 then
    ""
  else
    (s[n-1] + reverse_string(s[..n-1]))
}

// Helper function to convert a char to a string of length 1
function as_string(c: char): string
{
  // This function is no longer needed directly as Dafny allows char + string concatenation in recent versions.
  // Keeping it as a placeholder if older Dafny versions are targeted or if specific string construction is needed.
  // For the given problem, the direct char + string concatenation is sufficient.
  new string([c])
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
  var n := |s];
  // `chars` is not strictly needed for this method's return value
  // var chars := new char[n];
  var has_alpha := false;

  if n == 0 {
    return "";
  }

  // Check if there's any alpha character
  for i := 0 to n - 1
    invariant 0 <= i <= n
    invariant (exists k :: 0 <= k < i && is_alpha(s[k])) ==> has_alpha
  {
    if is_alpha(s[i]) {
      has_alpha := true;
    }
  }

  if !has_alpha {
    var result_chars := new char[n];
    for i := 0 to n - 1
      invariant 0 <= i <= i <= n
      invariant forall k :: 0 <= k < i ==> result_chars[k] == s[n - 1 - k]
    {
      result_chars[i] := s[n - 1 - i];
    }
    return new string(result_chars);
  } else {
    var result_chars := new char[n];
    for i := 0 to n - 1
      invariant 0 <= i <= n
      invariant forall k :: 0 <= k < i ==> result_chars[k] == (if is_alpha(s[k]) then flip_case(s[k]) else s[k])
    {
      if is_alpha(s[i]) {
        result_chars[i] := flip_case(s[i]);
      } else {
        result_chars[i] := s[i];
      }
    }
    return new string(result_chars);
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