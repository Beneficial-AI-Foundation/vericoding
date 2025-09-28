// <vc-preamble>

function SumSeq(s: seq<int>): int
{
    if |s| == 0 then 0
    else s[0] + SumSeq(s[1..])
}

function ProductSeq(s: seq<int>): int
{
    if |s| == 0 then 1
    else s[0] * ProductSeq(s[1..])
}
lemma SumSeqAppend(s: seq<int>, x: int)
    ensures SumSeq(s + [x]) == SumSeq(s) + x
{
    if |s| == 0 {
        assert s + [x] == [x];
        assert SumSeq([x]) == x + SumSeq([]);
        assert SumSeq([]) == 0;
    } else {
        assert s == [s[0]] + s[1..];
        assert s + [x] == [s[0]] + (s[1..] + [x]);
        SumSeqAppend(s[1..], x);
    }
}

lemma ProductSeqAppend(s: seq<int>, x: int)
    ensures ProductSeq(s + [x]) == ProductSeq(s) * x
{
    if |s| == 0 {
        assert s + [x] == [x];
        assert ProductSeq([x]) == x * ProductSeq([]);
        assert ProductSeq([]) == 1;
    } else {
        assert s == [s[0]] + s[1..];
        assert s + [x] == [s[0]] + (s[1..] + [x]);
        ProductSeqAppend(s[1..], x);
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): lemma that relates slice append */
lemma SliceAppendLemma(s: seq<int>, i: int)
  requires 0 <= i < |s|
  ensures s[..i] + [s[i]] == s[..i+1]
{
  assert s == s[..i] + s[i..];
  assert s[i..] == [s[i]] + s[i+1..];
  assert s == s[..i] + ([s[i]] + s[i+1..]);
  assert s[..i+1] == s[..i] + [s[i]];
}

// </vc-helpers>

// <vc-spec>
method sum_product(numbers: seq<int>) returns (sum: int, product: int)
    ensures sum == SumSeq(numbers)
    ensures product == ProductSeq(numbers)
    ensures |numbers| == 0 ==> sum == 0 && product == 1
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): iterative accumulation with final assertions to discharge postconditions */
  var i := 0;
  sum := 0;
  product := 1;
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant sum == SumSeq(numbers[..i])
    invariant product == ProductSeq(numbers[..i])
  {
    SliceAppendLemma(numbers, i);
    SumSeqAppend(numbers[..i], numbers[i]);
    ProductSeqAppend(numbers[..i], numbers[i]);
    sum := sum + numbers[i];
    product := product * numbers[i];
    i := i + 1;
  }
  // help the verifier conclude the postconditions
  assert i == |numbers|;
  assert numbers[..i] == numbers;
  assert SumSeq(numbers[..i]) == SumSeq(numbers);
  assert ProductSeq(numbers[..i]) == ProductSeq(numbers);
}
// </vc-code>
