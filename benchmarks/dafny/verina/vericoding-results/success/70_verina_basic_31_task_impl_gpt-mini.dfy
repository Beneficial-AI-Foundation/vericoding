// <vc-preamble>
predicate IsLowerCase(c: char)
{
    'a' <= c && c <= 'z'
}

function ShiftMinus32(c: char): char
    requires 'a' <= c <= 'z'
{
    (c as int - 32) as char
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): proves ShiftMinus32 maps lowercase to uppercase */
lemma ShiftMinus32_produces_upper(c: char)
  requires IsLowerCase(c)
  ensures 'A' <= ShiftMinus32(c) <= 'Z'
{
  var ci := c as int;
  var ri := ShiftMinus32(c) as int;
  assert 'a' as int <= ci <= 'z' as int;
  assert ri == ci - 32;
  assert ri >= 'a' as int - 32;
  assert ri <= 'z' as int - 32;
  assert 'a' as int - 32 == 'A' as int;
  assert 'z' as int - 32 == 'Z' as int;
  assert 'A' as int <= ri <= 'Z' as int;
}

/* helper modified by LLM (iteration 4): shows ShiftMinus32 result is not lowercase */
lemma ShiftMinus32_not_lower(c: char)
  requires IsLowerCase(c)
  ensures !IsLowerCase(ShiftMinus32(c))
{
  ShiftMinus32_produces_upper(c);
  assert 'A' <= ShiftMinus32(c) <= 'Z';
  assert !('a' <= ShiftMinus32(c) && ShiftMinus32(c) <= 'z');
}
// </vc-helpers>

// <vc-spec>
method ToUppercase(s: string) returns (result: string)
    ensures
        |result| == |s|
    ensures
        forall i :: 0 <= i < |s| ==> 
            var c := s[i];
            var r := result[i];
            if IsLowerCase(c) then
                r == ShiftMinus32(c)
            else
                r == c
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): build result by concatenating single-char sequences */
  var n := |s|;
  result := "";
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> 
      var c := s[j];
      var r := result[j];
      if IsLowerCase(c) then
        r == ShiftMinus32(c)
      else
        r == c
  {
    var c := s[i];
    if IsLowerCase(c) {
      result := result + [ShiftMinus32(c)];
    } else {
      result := result + [c];
    }
    i := i + 1;
  }
}
// </vc-code>
