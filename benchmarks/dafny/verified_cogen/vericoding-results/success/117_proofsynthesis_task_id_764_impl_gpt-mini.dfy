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
lemma CountDigitsRecursivelyBounds(s: seq<char>)
  ensures 0 <= CountDigitsRecursively(s) && CountDigitsRecursively(s) <= |s|
  decreases |s|
{
  if |s| == 0 {
  } else {
    var prev := s[..|s|-1];
    CountDigitsRecursivelyBounds(prev);
    if IsDigit(s[|s|-1]) {
      assert CountDigitsRecursively(s) == CountDigitsRecursively(prev) + 1;
      assert 0 <= CountDigitsRecursively(prev);
      assert CountDigitsRecursively(prev) + 1 <= |prev| + 1;
      assert |prev| + 1 == |s|;
    } else {
      assert CountDigitsRecursively(s) == CountDigitsRecursively(prev);
    }
    assert 0 <= CountDigitsRecursively(s);
    assert CountDigitsRecursively(s) <= |s|;
  }
}
// </vc-helpers>

// <vc-spec>
method CountDigits(text: array<char>) returns (count: int)
    ensures 0 <= count <= text.Length
    ensures CountDigitsRecursively(text[..]) == count
// </vc-spec>
// <vc-code>
{
  count := CountDigitsRecursively(text[..]);
  CountDigitsRecursivelyBounds(text[..]);
}
// </vc-code>
