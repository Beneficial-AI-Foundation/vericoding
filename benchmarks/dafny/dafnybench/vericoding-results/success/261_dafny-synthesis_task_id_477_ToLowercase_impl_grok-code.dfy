predicate IsUpperCase(c : char)
{
    65 <= c as int <= 90
}

predicate IsUpperLowerPair(C : char, c : char)
{
    (C as int) == (c as int) - 32
}

function Shift32(c : char) :  char
{
    ((c as int + 32) % 128) as char
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ToLowercase(s: string) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==>  if IsUpperCase(s[i]) then IsUpperLowerPair(s[i], v[i]) else v[i] == s[i]
// </vc-spec>
// <vc-code>
{
  var chars: seq<char> := [];
  var i: int := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |chars| == i
    invariant forall k :: 0 <= k < i ==> if IsUpperCase(s[k]) then IsUpperLowerPair(s[k], chars[k]) else chars[k] == s[k]
  {
    var newChar := if IsUpperCase(s[i]) then Shift32(s[i]) else s[i];
    chars := chars + [newChar];
    i := i + 1;
  }
  v := chars;
}
// </vc-code>

