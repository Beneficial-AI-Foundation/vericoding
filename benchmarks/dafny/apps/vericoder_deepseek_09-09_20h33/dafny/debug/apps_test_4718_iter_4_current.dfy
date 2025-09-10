predicate ValidInput(dateStr: string) 
{
    |dateStr| == 10 && dateStr[0..4] == "2017"
}

predicate ValidOutput(input: string, output: string)
    requires |input| >= 4
{
    output == "2018" + input[4..] &&
    |output| == 10 &&
    output[0..4] == "2018" &&
    output[4..] == input[4..]
}

// <vc-helpers>
lemma StringSliceProperties(s: string, start: int, end: int)
  requires 0 <= start <= end <= |s|
  ensures s[start..end] == s[start..end]
{
}

lemma StringConcatProperties(s1: string, s2: string)
  ensures |s1 + s2| == |s1| + |s2|
{
}

lemma StringEqualityLemma(s1: string, s2: string, s3: string, s4: string)
  requires s1 == s3 && s2 == s4
  ensures s1 + s2 == s3 + s4
{
}

lemma StringSliceConcatLemma(s1: string, s2: string, n: int)
  requires 0 <= n <= |s1|
  ensures (s1 + s2)[0..n] == s1[0..n]
{
}

lemma StringSliceConcatLemma2(s1: string, s2: string, n: int)
  requires 0 <= n <= |s1|
  ensures (s1 + s2)[n..] == s1[n..] + s2
{
}

lemma ValidInputLength(dateStr: string)
  requires ValidInput(dateStr)
  ensures |dateStr| == 10
{
}
// </vc-helpers>

// <vc-spec>
method solve(dateStr: string) returns (result: string)
    requires ValidInput(dateStr)
    ensures ValidOutput(dateStr, result)
// </vc-spec>
// <vc-code>
{
  ValidInputLength(dateStr);
  result := "2018" + dateStr[4..];
  assert result == "2018" + dateStr[4..];
  assert |result| == 4 + (|dateStr| - 4) by {
    StringConcatProperties("2018", dateStr[4..]);
  };
  assert result[0..4] == "2018" by {
    StringSliceConcatLemma("2018", dateStr[4..], 4);
  };
  assert result[4..] == dateStr[4..] by {
    StringSliceConcatLemma2("2018", dateStr[4..], 4);
  };
}
// </vc-code>

