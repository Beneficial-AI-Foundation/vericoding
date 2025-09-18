// <vc-preamble>
/* Helper function to check if a character is uppercase */
predicate IsUppercase(c: char)
{
    'A' <= c <= 'Z'
}

/* Helper function to shift character by 32 positions */
function Shift32(c: char): char
    requires 'A' <= c <= 'Z'
{
    ((c as int) + 32) as char
}
// </vc-preamble>

// <vc-helpers>
function Lower(c: char): char { if IsUppercase(c) then Shift32(c) else c }
lemma LowerCorrect(c: char)
  ensures IsUppercase(c) ==> Lower(c) == Shift32(c)
  ensures !IsUppercase(c) ==> Lower(c) == c
{ }
// </vc-helpers>

// <vc-spec>
method ToLowercase(s: seq<char>) returns (result: seq<char>)
    ensures
        |result| == |s| &&
        forall i :: 0 <= i < |s| ==> 
            if IsUppercase(s[i]) then
                result[i] == Shift32(s[i])
            else
                result[i] == s[i]
// </vc-spec>
// <vc-code>
{
  var r: seq<char> := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |r| == i
    invariant forall j :: 0 <= j < i ==> (if IsUppercase(s[j]) then r[j] == Shift32(s[j]) else r[j] == s[j])
    decreases |s| - i
  {
    var ch := s[i];
    var lc := if IsUppercase(ch) then Shift32(ch) else ch;
    r := r + [lc];
    i := i + 1;
  }
  result := r;
}
// </vc-code>
