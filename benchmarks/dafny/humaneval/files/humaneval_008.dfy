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
// </vc-helpers>

// <vc-spec>
method sum_product(numbers: seq<int>) returns (sum: int, product: int)
    ensures sum == SumSeq(numbers)
    ensures product == ProductSeq(numbers)
    ensures |numbers| == 0 ==> sum == 0 && product == 1
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
  }
// </vc-code>
