// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
function reverseSeq<T>(s: seq<T>): seq<T> {
  if |s| <= 1 then s else reverseSeq(s[1..]) + [s[0]]
}

// </vc-helpers>

// <vc-spec>
method ReverseWords(words_str: string) returns (result: string)
// </vc-spec>
// <vc-code>
{
  // impl-start
  result := words_str;
  // impl-end
}

// </vc-code>
