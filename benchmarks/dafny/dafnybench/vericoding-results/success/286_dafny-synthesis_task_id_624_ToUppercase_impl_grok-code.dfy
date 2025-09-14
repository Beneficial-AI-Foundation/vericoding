predicate IsLowerCase(c : char)
{
    97 <= c as int <= 122
}

predicate IsLowerUpperPair(c : char, C : char)
{
    (c as int) == (C as int) + 32
}

function ShiftMinus32(c : char) :  char
{
    ((c as int - 32) % 128) as char
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ToUppercase(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==>  if IsLowerCase(s[i]) then IsLowerUpperPair(s[i], v[i]) else v[i] == s[i]
// </vc-spec>
// <vc-code>
{
  var result: string := [];
  var i: int := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> if IsLowerCase(s[k]) then IsLowerUpperPair(s[k], result[k]) else result[k] == s[k]
  {
    var c := s[i];
    if IsLowerCase(c) {
      result := result + [ShiftMinus32(c)];
    } else {
      result := result + [c];
    }
    i := i + 1;
  }
  v := result;
}
// </vc-code>

