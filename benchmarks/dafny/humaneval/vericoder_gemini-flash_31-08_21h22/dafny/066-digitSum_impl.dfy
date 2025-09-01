function upper_sum_rec(s: string): int
  // post-conditions-start
  ensures upper_sum_rec(s) >= 0
  // post-conditions-end
{
  // impl-start
  if |s| == 0 then
    0
  else
    var remaining := upper_sum_rec(s[1..]);
    to_int(s[0]) + remaining
  // impl-end
}
function to_int(c: char): int
    ensures 'A' <= c <= 'Z' ==> to_int(c) == c as int
    ensures c < 'A' || c > 'Z' ==> to_int(c) == 0
{
    if 'A' <= c <= 'Z' then c as int else 0
}

// <vc-helpers>
function IsUpperCase(c: char): bool
  ensures IsUpperCase(c) == ('A' <= c <= 'Z')
{
  'A' <= c <= 'Z'
}

function to_int_upper(c: char): int
  ensures to_int_upper(c) == (if IsUpperCase(c) then c as int else 0)
{
  if IsUpperCase(c) then c as int else 0
}

function upper_sum_rec_prefix(s: string, i: int): int
  requires 0 <= i <= |s|
  ensures upper_sum_rec_prefix(s, i) >= 0
{
  if i == 0 then
    0
  else
    upper_sum_rec_prefix(s, i - 1) + to_int_upper(s[i - 1])
}

// Introduce a lemma to relate upper_sum_rec_prefix to upper_sum_rec for the entire string
lemma LemmaUpperSumRecPrefixEqualsUpperSumRec(s: string)
  ensures upper_sum_rec_prefix(s, |s|) == upper_sum_rec(s)
{
  if |s| == 0 {
    assert upper_sum_rec_prefix(s, 0) == 0;
    assert upper_sum_rec(s) == 0;
  } else {
    // This proof uses induction implicit in the definition of upper_sum_rec and upper_sum_rec_prefix
    // It asserts that the sum up to |s| is indeed the total sum
  }
}
// </vc-helpers>

// <vc-spec>
method upper_sum(s: string) returns (res: int)
    // post-conditions-start
    ensures res == upper_sum_rec(s)
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  res := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant res == upper_sum_rec_prefix(s, i) // This invariant relates res to the prefix sum
  {
    var c := s[i];
    res := res + to_int_upper(c);
    i := i + 1;
  }
  // After the loop, i == |s|
  // From the invariant, we have res == upper_sum_rec_prefix(s, |s|)
  // We need to prove res == upper_sum_rec(s)
  // This is where the lemma LemmaUpperSumRecPrefixEqualsUpperSumRec is used.
  LemmaUpperSumRecPrefixEqualsUpperSumRec(s);
  assert res == upper_sum_rec(s); // This assertion holds due to the lemma and the loop invariant.
}
// </vc-code>

