predicate ValidInput(s: string) {
    |s| == 4 && forall i :: 0 <= i < |s| ==> s[i] == '+' || s[i] == '-'
}

function CountChar(s: string, c: char): int
{
    if |s| == 0 then 0
    else (if s[0] == c then 1 else 0) + CountChar(s[1..], c)
}

function CalculateSum(s: string): int
    requires ValidInput(s)
{
    CountChar(s, '+') - CountChar(s, '-')
}

// <vc-helpers>
function CountChar_iter(s: string, c: char, start: int, end_idx: int) : int
  requires 0 <= start <= end_idx <= |s|
  decreases end_idx - start
{
  if start == end_idx then 0
  else (if s[start] == c then 1 else 0) + CountChar_iter(s, c, start + 1, end_idx)
}

lemma CountChar_is_CountChar_iter(s: string, c: char)
  ensures CountChar(s, c) == CountChar_iter(s, c, 0, |s|)
{
  if |s| == 0 {
    // Base case: s is empty
  } else {
    // Recursive step: leverage the lemma on the rest of the string
    CountChar_is_CountChar_iter(s[1..], c);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: int)
    requires ValidInput(s)
    ensures result == CalculateSum(s)
// </vc-spec>
// <vc-code>
{
  var plusCount := 0;
  var minusCount := 0;

  CountChar_is_CountChar_iter(s, '+');
  CountChar_is_CountChar_iter(s, '-');

  // Since ValidInput(s) ensures |s| == 4, we can iterate 4 times.
  // The loop invariant will ensure plusCount accumulates '+' and minusCount accumulates '-'
  // until they equal CountChar_iter(s, '+', 0, |s|) and CountChar_iter(s, '-', 0, |s|) respectively.
  // This is because we know CountChar_iter(s, c, 0, |s|) is equivalent to CountChar(s, c).
  for i := 0 to |s| - 1
    invariant 0 <= i <= |s|
    invariant plusCount == CountChar_iter(s, '+', 0, i)
    invariant minusCount == CountChar_iter(s, '-', 0, i)
  {
    if s[i] == '+' {
      plusCount := plusCount + 1;
    } else if s[i] == '-' {
      minusCount := minusCount + 1;
    }
  }

  // After the loop, plusCount equals CountChar_iter(s, '+', 0, |s|)
  // and minusCount equals CountChar_iter(s, '-', 0, |s|)
  // which by CountChar_is_CountChar_iter lemma are equal to CountChar(s, '+') and CountChar(s, '-')
  result := plusCount - minusCount;
}
// </vc-code>

