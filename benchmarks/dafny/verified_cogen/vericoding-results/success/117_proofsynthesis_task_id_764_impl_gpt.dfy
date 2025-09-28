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
/* helper modified by LLM (iteration 2): function mapping a char to its digit contribution (0 or 1) */
function DigitContribution(c: char): int { if IsDigit(c) then 1 else 0 }

/* helper modified by LLM (iteration 2): bound on DigitContribution to help arithmetic in loop */
lemma DigitContributionBounds(c: char)
  ensures 0 <= DigitContribution(c) <= 1
{
  if IsDigit(c) {
  } else {
  }
}

/* helper modified by LLM (iteration 2): snoc lemma for CountDigitsRecursively over sequences */
lemma CountDigitsSnocLemma(s: seq<char>, c: char)
  ensures CountDigitsRecursively(s + [c]) == CountDigitsRecursively(s) + DigitContribution(c)
{
  assert |s + [c]| == |s| + 1;
  assert (s + [c])[..|s|] == s;
  assert (s + [c])[|s|] == c;
}

/* helper modified by LLM (iteration 2): relate array prefix extension to snoc on sequences */
lemma ArraySliceSnoc(a: array<char>, i: int)
  requires 0 <= i < a.Length
  ensures a[..i+1] == a[..i] + [a[i]]
{
}

// </vc-helpers>

// <vc-spec>
method CountDigits(text: array<char>) returns (count: int)
    ensures 0 <= count <= text.Length
    ensures CountDigitsRecursively(text[..]) == count
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): iterative count with maintained correspondence to recursive spec via lemmas */
  var i := 0;
  var acc := 0;
  while i < text.Length
    invariant 0 <= i <= text.Length
    invariant 0 <= acc <= i
    invariant acc == CountDigitsRecursively(text[..i])
  {
    var c := text[i];
    DigitContributionBounds(c);
    CountDigitsSnocLemma(text[..i], c);
    ArraySliceSnoc(text, i);
    acc := acc + DigitContribution(c);
    i := i + 1;
  }
  count := acc;
  assert text[..] == text[..text.Length];
}
// </vc-code>
