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
/* helper modified by LLM (iteration 2): Proves prefix extended by current element equals next-length prefix */
lemma PrefixSnocEquality<T>(s: seq<T>, i: int)
    requires 0 <= i < |s|
    ensures s[..i] + [s[i]] == s[..i+1]
{
    assert s[i..i+1] == [s[i]];
    assert s[..i] + s[i..i+1] == s[..i+1];
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
  /* code modified by LLM (iteration 2): Implemented loop accumulating sum/product with invariants and final assertions */
  var i := 0;
  sum := 0;
  product := 1;
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant sum == SumSeq(numbers[..i])
    invariant product == ProductSeq(numbers[..i])
  {
    var oldI := i;
    var x := numbers[oldI];
    sum := sum + x;
    product := product * x;
    SumSeqAppend(numbers[..oldI], x);
    ProductSeqAppend(numbers[..oldI], x);
    i := oldI + 1;
    PrefixSnocEquality(numbers, oldI);
    assert numbers[..i] == numbers[..oldI] + [x];
  }
  assert i == |numbers|;
  assert numbers[..i] == numbers;
}
// </vc-code>
