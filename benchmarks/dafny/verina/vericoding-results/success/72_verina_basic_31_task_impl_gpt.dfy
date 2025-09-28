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
function UpperChar(c: char): char
{
    if IsLowerCase(c) then ShiftMinus32(c) else c
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
  var i := 0;
  result := "";
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==>
      var cj := s[j];
      var rj := result[j];
      if IsLowerCase(cj) then rj == ShiftMinus32(cj) else rj == cj
  {
    var c := s[i];
    var rc := UpperChar(c);
    result := result + [rc];
    i := i + 1;
  }
}
// </vc-code>
