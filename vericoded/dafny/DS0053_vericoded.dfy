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
/* helper modified by LLM (iteration 3): unfold SumRange for non-negative lengths */
lemma SumRangeUnfold(a: seq<int>, start: int, len: int)
    requires 0 <= start && 0 <= len && start + len <= |a|
    ensures SumRange(a, start, len) == (if len == 0 then 0 else a[start] + SumRange(a, start + 1, len - 1))
    decreases len
{
    if len == 0 {
    } else {
        SumRangeUnfold(a, start + 1, len - 1);
        assert SumRange(a, start, len) == a[start] + SumRange(a, start + 1, len - 1);
    }
}

/* helper modified by LLM (iteration 3): relate SumRange(len+1) to SumRange(len) plus last element */
lemma SumRangeAppend(a: seq<int>, start: int, len: int)
    requires 0 <= start && 0 <= len && start + len + 1 <= |a|
    ensures SumRange(a, start, len + 1) == SumRange(a, start, len) + a[start + len]
    decreases len
{
    if len == 0 {
        SumRangeUnfold(a, start, 1);
        assert SumRange(a, start, 0) == 0;
        assert SumRange(a, start, 1) == a[start];
    } else {
        SumRangeUnfold(a, start, len + 1);
        SumRangeUnfold(a, start, len);
        SumRangeAppend(a, start + 1, len - 1);
        assert SumRange(a, start, len + 1) == a[start] + SumRange(a, start + 1, len);
        assert SumRange(a, start, len) == a[start] + SumRange(a, start + 1, len - 1);
        assert SumRange(a, start + 1, len) == SumRange(a, start + 1, len - 1) + a[start + len];
        assert SumRange(a, start, len + 1) == SumRange(a, start, len) + a[start + len];
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
  /* code modified by LLM (iteration 3): iterative sum with invariant, handling negative start */
  if start < 0 {
    result := 0;
    return;
  }
  var s := 0;
  var i := start;
  while i < finish
    invariant start <= i <= finish
    invariant s == SumRange(a[..], start, i - start)
  {
    var oldLen := i - start;
    SumRangeAppend(a[..], start, oldLen);
    s := s + a[i];
    i := i + 1;
  }
  result := s;
}

// </vc-code>
