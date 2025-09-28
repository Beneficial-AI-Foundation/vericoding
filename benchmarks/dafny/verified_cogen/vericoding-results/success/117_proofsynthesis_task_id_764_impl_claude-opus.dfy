// <vc-preamble>
predicate IsDigit(c: char)
{
    (c as int) >= 48 && (c as int) <= 57
}

function CountDigitsRecursively(s: seq<char>): int
    decreases |s|
{
    if |s| == 0 then
        0
    else
        CountDigitsRecursively(s[..|s|-1]) + (if IsDigit(s[|s|-1]) then 1 else 0)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added lemma to prove relationship between recursive counting on prefixes */
lemma CountDigitsPrefix(s: seq<char>, i: int)
    requires 0 <= i < |s|
    ensures CountDigitsRecursively(s[..i+1]) == CountDigitsRecursively(s[..i]) + (if IsDigit(s[i]) then 1 else 0)
{
    if i == |s| - 1 {
        assert s[..i+1] == s;
    } else {
        assert s[..i+1][..|s[..i+1]|-1] == s[..i];
    }
}
// </vc-helpers>

// <vc-spec>
method CountDigits(text: array<char>) returns (count: int)
    ensures 0 <= count <= text.Length
    ensures CountDigitsRecursively(text[..]) == count
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed loop invariant and added lemma call to maintain invariant */
{
  count := 0;
  var i := 0;
  while i < text.Length
    invariant 0 <= i <= text.Length
    invariant 0 <= count <= i
    invariant count == CountDigitsRecursively(text[..i])
  {
    CountDigitsPrefix(text[..], i);
    if IsDigit(text[i]) {
      count := count + 1;
    }
    i := i + 1;
  }
  assert text[..i] == text[..text.Length] == text[..];
}
// </vc-code>
