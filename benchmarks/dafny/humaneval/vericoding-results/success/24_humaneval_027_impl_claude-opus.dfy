// <vc-preamble>

predicate IsLowercase(c: char) {
    'a' <= c <= 'z'
}

predicate IsUppercase(c: char) {
    'A' <= c <= 'Z'
}

function FlipChar(c: char): char {
    if IsLowercase(c) then c - 'a' + 'A'
    else if IsUppercase(c) then c - 'A' + 'a'
    else c
}

predicate ValidFlipCase(s: string, result: string) {
    |result| == |s| &&
    forall i :: 0 <= i < |s| ==> result[i] == FlipChar(s[i])
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method flip_case(s: string) returns (result: string)
    ensures ValidFlipCase(s, result)
// </vc-spec>
// <vc-code>
{
  var chars := [];
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant |chars| == i
    invariant forall j :: 0 <= j < i ==> chars[j] == FlipChar(s[j])
  {
    chars := chars + [FlipChar(s[i])];
  }
  result := chars;
}
// </vc-code>
