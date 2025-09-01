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

lemma string_slice_preserves_length(s: string, start: int, end: int)
    requires 0 <= start <= end <= |s|
    ensures |s[start..end]| == end - start
{
}

lemma string_concat_length(a: string, b: string)
    ensures |a + b| == |a| + |b|
{
}

lemma string_slice_concat_property(s: string, i: int, c: char)
    requires 0 <= i < |s|
    ensures s[..i] + [c] + s[i+1..] == s[0..i] + [c] + s[i+1..|s|]
{
}

lemma string_char_at_index(s: string, i: int)
    requires 0 <= i < |s|
    ensures |s[..i]| == i
    ensures |s[i+1..]| == |s| - i - 1
{
}
// </vc-helpers>
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
    invariant |S| == |s|
    invariant forall j :: 0 <= j < i ==> (lower(s[j]) <==> upper(S[j]))
    invariant forall j :: 0 <= j < i ==> (upper(s[j]) <==> lower(S[j]))
    invariant forall j :: i <= j < |s| ==> S[j] == s[j]
  {
    var c := s[i];
    var new_char := flip_char(c);
    S := S[..i] + [new_char] + S[i+1..];
    
    // Prove the invariants for the updated character at index i
    assert S[i] == new_char;
    assert lower(s[i]) <==> upper(S[i]) by {
      if alpha(c) {
        flip_char_flips_lower(c);
        flip_char_flips_upper(c);
      } else {
        assert flip_char(c) == c;
      }
    }
    assert upper(s[i]) <==> lower(S[i]) by {
      if alpha(c) {
        flip_char_flips_lower(c);
        flip_char_flips_upper(c);
      } else {
        assert flip_char(c) == c;
      }
    }
    
    // Prove that other characters remain unchanged
    assert forall j :: 0 <= j < i ==> S[j] == old(S)[j];
    assert forall j :: i+1 <= j < |s| ==> S[j] == old(S)[j];
    
    i := i + 1;
  }
}
// </vc-code>

