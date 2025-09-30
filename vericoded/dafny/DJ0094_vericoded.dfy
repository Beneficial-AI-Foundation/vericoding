// <vc-preamble>
predicate IsLowerCase(c: char)
{
    (c as int) >= 97 && (c as int) <= 122
}

predicate IsUpperCase(c: char)
{
    (c as int) >= 65 && (c as int) <= 90
}

function CountUppercaseRecursively(s: seq<char>): int
    decreases |s|
{
    if |s| == 0 then
        0
    else
        CountUppercaseRecursively(s[..|s|-1]) + (if IsUpperCase(s[|s|-1]) then 1 else 0)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added lemma to prove loop invariant maintenance */
lemma CountUppercaseStep(s: seq<char>, i: int)
  requires 0 <= i < |s|
  ensures CountUppercaseRecursively(s[..i+1]) == CountUppercaseRecursively(s[..i]) + (if IsUpperCase(s[i]) then 1 else 0)
{
  var prefix := s[..i+1];
  assert prefix[..|prefix|-1] == s[..i];
  assert prefix[|prefix|-1] == s[i];
}
// </vc-helpers>

// <vc-spec>
method CountUppercase(text: array<char>) returns (count: nat)
    ensures 0 <= count <= text.Length
    ensures CountUppercaseRecursively(text[..]) == count as int
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed loop invariant and added non-negativity invariant */
{
  count := 0;
  var i := 0;
  while i < text.Length
    invariant 0 <= i <= text.Length
    invariant 0 <= count <= i
    invariant count == CountUppercaseRecursively(text[..i])
  {
    CountUppercaseStep(text[..], i);
    if IsUpperCase(text[i]) {
      count := count + 1;
    }
    i := i + 1;
  }
  assert text[..i] == text[..text.Length] == text[..];
}
// </vc-code>
