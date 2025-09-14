// <vc-preamble>
function sum_chars_rec(list: seq<string>): nat
{
  if |list| == 0 then 0
  else |list[0]| + sum_chars_rec(list[1..])
}
// </vc-preamble>

// <vc-helpers>
lemma Lemma_SumCharsRecAppend(s1: seq<string>, s2: seq<string>)
  ensures sum_chars_rec(s1 + s2) == sum_chars_rec(s1) + sum_chars_rec(s2)
  decreases |s1|
{
  if |s1| > 0 {
    Lemma_SumCharsRecAppend(s1[1..], s2);
  }
}
// </vc-helpers>

// <vc-spec>
method SumChars(list: seq<string>) returns (sum: nat)

  ensures sum == sum_chars_rec(list)
// </vc-spec>
// <vc-code>
{
  sum := 0;
  var i := 0;
  while i < |list|
    invariant 0 <= i <= |list|
    invariant sum == sum_chars_rec(list[..i])
  {
    Lemma_SumCharsRecAppend(list[..i], [list[i]]);
    sum := sum + |list[i]|;
    i := i + 1;
  }
}
// </vc-code>
