// <vc-preamble>
function pow2(n: nat): nat
    ensures pow2(n) > 0
{
  if n == 0 then 1 else 2 * pow2(n - 1)
}

function shift_right_int(x: int, n: nat): int
    requires pow2(n) > 0
{
  if x >= 0 then
    x / pow2(n)
  else
    -((((-x) - 1) / pow2(n)) + 1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Positivity lemma for pow2 used to satisfy precondition of shift_right_int */
lemma Pow2Positive(n: nat)
  ensures pow2(n) > 0
{
  if n == 0 {
    assert pow2(0) == 1;
  } else {
    Pow2Positive(n - 1);
    assert pow2(n) == 2 * pow2(n - 1);
    assert 2 > 0;
    assert pow2(n - 1) > 0;
    assert pow2(n) > 0;
  }
}
// </vc-helpers>

// <vc-spec>
method right_shift(a: array<int>, b: array<int>) returns (result: array<int>)
    requires a.Length == b.Length
    requires forall i :: 0 <= i < b.Length ==> 0 <= b[i] < 64
    ensures result.Length == a.Length
    ensures forall i :: 0 <= i < result.Length ==> 
        result[i] == shift_right_int(a[i], b[i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Element-wise arithmetic right shift without null comparison invariant to avoid warnings */
  var n := a.Length;
  result := new int[n];
  var i: int := 0;
  while i < n
    invariant 0 <= i <= n
    invariant a.Length == n && b.Length == n
    invariant result.Length == n
    invariant forall j :: 0 <= j < i ==> result[j] == shift_right_int(a[j], b[j])
  {
    assert 0 <= i;
    assert i < n;
    assert i < b.Length;
    assert 0 <= b[i];
    var bi: nat := b[i] as nat;
    Pow2Positive(bi);
    result[i] := shift_right_int(a[i], bi);
    i := i + 1;
  }
}
// </vc-code>
