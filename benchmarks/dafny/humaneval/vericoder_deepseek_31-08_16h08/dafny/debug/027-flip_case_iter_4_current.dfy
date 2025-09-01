function lower(c: char) : bool
    {
        'a' <= c <= 'z'
    }
function upper(c: char) : bool
    {
        'A' <= c <= 'Z'
    }
function alpha(c: char) : bool
    {
        lower(c) || upper(c)
    }
function flip_char(c: char) : (C: char)
        ensures lower(c) <==> upper(C)
        ensures upper(c) <==> lower(C)
    {
        if lower(c) then c - 'a' + 'A' else
        if upper(c) then c + 'a' - 'A' else c
    }

// <vc-helpers>
lemma flip_char_flips_lower(c: char)
    ensures lower(c) <==> upper(flip_char(c))
{
}

lemma flip_char_flips_upper(c: char)
    ensures upper(c) <==> lower(flip_char(c))
{
}

lemma flip_char_preserves_non_alpha(c: char)
    requires !alpha(c)
    ensures flip_char(c) == c
{
}

lemma flip_char_involutive(c: char)
    ensures flip_char(flip_char(c)) == c
{
    if lower(c) {
    } else if upper(c) {
    } else {
    }
}
// </vc-helpers>

// <vc-spec>
method flip_case(s: string) returns (S: string)
    // post-conditions-start
    ensures |S| == |s|
    ensures forall i :: 0 <= i < |s| ==> (lower(s[i]) <==> upper(S[i]))
    ensures forall i :: 0 <= i < |s| ==> (upper(s[i]) <==> lower(S[i]))
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  S := s;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall j :: 0 <= j < i ==> (lower(s[j]) <==> upper(S[j]))
    invariant forall j :: 0 <= j < i ==> (upper(s[j]) <==> lower(S[j]))
    invariant |S| == |s|
  {
    var c := s[i];
    if alpha(c) {
      S := S[..i] + [flip_char(c)] + S[i+1..];
    }
    i := i + 1;
  }
}
// </vc-code>

