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
/* helper modified by LLM (iteration 2): prove extension property of SumRange when increasing length by 1 */
lemma SumRange_ExtendRightLen(a: seq<int>, start: int, len: int)
  requires 0 <= start
  requires 0 <= len
  requires start + len < |a|
  ensures SumRange(a, start, len + 1) == SumRange(a, start, len) + a[start + len]
  decreases len
{
  if len == 0 {
    assert start < |a|;
    assert start + 1 <= |a|;
    assert SumRange(a, start, 1) == a[start] + SumRange(a, start + 1, 0);
    assert SumRange(a, start, 0) == 0;
  } else {
    assert len + 1 > 0 && 0 <= start && start + (len + 1) <= |a|;
    assert SumRange(a, start, len + 1) == a[start] + SumRange(a, start + 1, len);

    assert 0 <= start + 1;
    assert 0 <= len - 1;
    assert start + 1 + (len - 1) < |a|; // since start + len < |a|
    SumRange_ExtendRightLen(a, start + 1, len - 1);

    assert len > 0 && 0 <= start && start + len <= |a|;
    assert SumRange(a, start, len) == a[start] + SumRange(a, start + 1, len - 1);

    calc {
      SumRange(a, start, len + 1);
      == { }
      a[start] + SumRange(a, start + 1, len);
      == { SumRange_ExtendRightLen(a, start + 1, len - 1); }
      a[start] + (SumRange(a, start + 1, len - 1) + a[start + len]);
      == { }
      (a[start] + SumRange(a, start + 1, len - 1)) + a[start + len];
      == { }
      SumRange(a, start, len) + a[start + len];
    }
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
  /* code modified by LLM (iteration 2): implement SumArray via iterative accumulation using helper lemma */
  if start < 0 {
    result := 0;
  } else {
    var i := start;
    var acc := 0;
    while i < finish
      invariant start <= i <= finish
      invariant 0 <= i
      invariant acc == SumRange(a[..], start, i - start)
      invariant finish <= a.Length
      decreases finish - i
    {
      var oldI := i;
      acc := acc + a[i];
      i := i + 1;
      assert 0 <= start;
      assert 0 <= oldI - start;
      assert oldI < finish;
      assert finish <= a.Length;
      assert oldI < a.Length;
      assert SumRange(a[..], start, i - start) == SumRange(a[..], start, oldI - start) + a[oldI] by {
        SumRange_ExtendRightLen(a[..], start, oldI - start);
      }
      assert acc == SumRange(a[..], start, i - start);
    }
    result := acc;
  }
}
// </vc-code>
