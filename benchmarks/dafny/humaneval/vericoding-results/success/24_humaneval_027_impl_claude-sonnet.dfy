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
  result := "";
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == FlipChar(s[j])
  {
    result := result + [FlipChar(s[i])];
    i := i + 1;
  }
}
// </vc-code>
