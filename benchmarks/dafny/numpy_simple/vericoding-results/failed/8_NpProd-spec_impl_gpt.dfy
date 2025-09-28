// <vc-preamble>
function ProdSpecHelper(a: seq<int>, start: int, finish: int): int
    requires 0 <= start <= finish <= |a|
    decreases finish - start
{
    if start >= finish then
        1
    else
        a[start] * ProdSpecHelper(a, start + 1, finish)
}

function ProdSpec(a: seq<int>): int {
    ProdSpecHelper(a, 0, |a|)
}

function ProdArraySpec(a: seq<int>, start: int, finish: int): int
    requires 0 <= start <= finish <= |a|
{
    ProdSpecHelper(a, start, finish)
}
// </vc-preamble>

// <vc-helpers>
lemma ProdSpecHelperMul(s: seq<int>, start: int, mid: int, finish: int)
    requires 0 <= start <= mid <= finish <= |s|
    ensures ProdSpecHelper(s, start, finish) ==
            ProdSpecHelper(s, start, mid) * ProdSpecHelper(s, mid, finish)
    decreases finish - start
{
    if start >= finish {
    } else if start < mid {
        ProdSpecHelperMul(s, start + 1, mid, finish);
    } else {
        assert start == mid;
    }
}

lemma ProdSpecHelperRangeOne(s: seq<int>, i: int)
    requires 0 <= i < |s|
    ensures ProdSpecHelper(s, i, i + 1) == s[i]
{
}

lemma ProdSpecEqualsArraySpec(s: seq<int>)
    ensures ProdSpec(s) == ProdArraySpec(s, 0, |s|)
{
}
// </vc-helpers>

// <vc-spec>
method Prod(a: array<int>) returns (result: int)
    ensures result == ProdSpec(a[..])
{
    assume {:axiom} false;
}

method ProdArray(a: array<int>, start: int, finish: int) returns (result: int)
    requires 0 <= start <= finish <= a.Length
    ensures result == ProdArraySpec(a[..], start, finish)
{
    assume {:axiom} false;
}

lemma {:axiom} ProdTheorem(a: array<int>)
    requires a.Length > 0
    ensures ProdSpec(a[..]) == ProdArraySpec(a[..], 0, a.Length) &&
            (forall i :: 0 <= i < a.Length && a[i] == 0 ==> ProdSpec(a[..]) == 0)
// </vc-spec>
// <vc-code>
{
  var r := ProdArray(a, 0, a.Length);
  result := r;
  ProdSpecEqualsArraySpec(a[..]);
}
{
  ghost var s := a[..];
  var i := start;
  var acc := 1;
  while i < finish
    invariant start <= i <= finish
    invariant s == a[..]
    invariant acc == ProdSpecHelper(s, start, i)
    decreases finish - i
  {
    assert 0 <= start <= i < |s|;
    assert a[i] == s[i];
    assert ProdSpecHelper(s, start, i + 1) == ProdSpecHelper(s, start, i) * ProdSpecHelper(s, i, i + 1) by {
      ProdSpecHelperMul(s, start, i, i + 1);
    };
    assert ProdSpecHelper(s, i, i + 1) == s[i] by {
      ProdSpecHelperRangeOne(s, i);
    };
    acc := acc * a[i];
    i := i + 1;
    assert acc == ProdSpecHelper(s, start, i);
  }
  result := acc;
  assert result == ProdSpecHelper(s, start, finish);
  assert s == a[..];
}
// </vc-code>
