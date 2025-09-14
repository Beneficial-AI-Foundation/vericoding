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
function ToUpperChar(c: char): char { if IsLowerCase(c) then ShiftMinus32(c) else c }
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
  var i := 0;
  result := s;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |result| == |s|
    invariant forall j :: 0 <= j < i ==> result[j] == ToUpperChar(s[j])
    invariant forall j :: i <= j < |s| ==> result[j] == s[j]
    decreases |s| - i
  {
    var c := s[i];
    var uc := ToUpperChar(c);
    result := result[0..i] + [uc] + s[i+1..];
    i := i + 1;
  }
}
// </vc-code>
