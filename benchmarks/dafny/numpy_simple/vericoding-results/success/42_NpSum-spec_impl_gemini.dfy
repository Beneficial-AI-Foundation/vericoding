// <vc-preamble>
function SumRange(a: seq<int>, start: int, len: int): int
    decreases len
{
    if len <= 0 || start < 0 || start + len > |a| then
        0
    else if len == 0 then
        0
    else
        a[start] + SumRange(a, start + 1, len - 1)
}

function SeqSum(a: seq<int>): int
{
    SumRange(a, 0, |a|)
}
// </vc-preamble>

// <vc-helpers>
lemma SumRangeAppend(a: seq<int>, s: int, len: int)
    requires 0 <= s && s + len <= |a|
    requires len > 0
    ensures SumRange(a, s, len) == SumRange(a, s, len - 1) + a[s + len - 1]
    decreases len
{
    if len > 1 {
        SumRangeAppend(a, s + 1, len - 1);
    }
}
// </vc-helpers>

// <vc-spec>
method Sum(a: array<int>) returns (result: int)
    ensures result == SeqSum(a[..])
{
    assume {:axiom} false;
}

method SumArray(a: array<int>, start: int, finish: int) returns (result: int)
    requires start <= finish && finish <= a.Length
    ensures result == SumRange(a[..], start, finish - start)
// </vc-spec>
// <vc-code>
{
  result := 0;
  if 0 <= start {
    var i := start;
    while i < finish
        invariant start <= i <= finish
        invariant result == SumRange(a[..], start, i - start)
    {
        SumRangeAppend(a[..], start, i - start + 1);
        result := result + a[i];
        i := i + 1;
    }
  }
}
// </vc-code>
