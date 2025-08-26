function NChoose2(n: int): int
{
  n * (n - 1) / 2
}

// sum of all integers in the range [lo, hi)
// (inclusive of lo, exclusive of hi)
function SumRange(lo: int, hi: int): int
  decreases hi - lo
{
  if lo >= hi then 0
  else SumRange(lo, hi - 1) + hi - 1
}

// dafny proves this automatically by induction
lemma SumRangeNChoose2(n: nat)
  ensures SumRange(0, n) == NChoose2(n)
{}

// <vc-helpers>
lemma SumRangeAdditive(lo: int, mid: int, hi: int)
  requires lo <= mid <= hi
  ensures SumRange(lo, hi) == SumRange(lo, mid) + SumRange(mid, hi)
{
  if mid == hi {
    assert SumRange(mid, hi) == 0;
  } else {
    SumRangeAdditive(lo, mid, hi - 1);
    calc {
      SumRange(lo, hi);
      == SumRange(lo, hi - 1) + hi - 1;
      == SumRange(lo, mid) + SumRange(mid, hi - 1) + hi - 1;
      == SumRange(lo, mid) + (SumRange(mid, hi - 1) + hi - 1);
      == SumRange(lo, mid) + SumRange(mid, hi);
    }
  }
}

lemma SumRangeStep(i: nat)
  ensures SumRange(0, i + 1) == SumRange(0, i) + i
{
  if i == 0 {
    calc {
      SumRange(0, 1);
      == SumRange(0, 0) + 0;
      == 0 + 0;
      == 0;
    }
  } else {
    calc {
      SumRange(0, i + 1);
      == SumRange(0, i) + i;
    }
  }
}

function BubbleSortBound(len: nat, i: nat): nat
  requires i <= len
{
  if i == 0 then 0
  else BubbleSortBound(len, i - 1) + (len - i)
}

lemma BubbleSortBoundCorrect(len: nat)
  ensures BubbleSortBound(len, len) == NChoose2(len)
{
  BubbleSortBoundSum(len, len);
  SumRangeNChoose2(len);
  calc {
    BubbleSortBound(len, len);
    == { BubbleSortBoundSum(len, len); }
    SumRange(0, len) - SumRange(0, len - len);
    == SumRange(0, len) - SumRange(0, 0);
    == SumRange(0, len) - 0;
    == SumRange(0, len);
    == { SumRangeNChoose2(len); }
    NChoose2(len);
  }
}

lemma BubbleSortBoundSum(len: nat, i: nat)
  requires i <= len
  ensures BubbleSortBound(len, i) == SumRange(0, len) - SumRange(0, len - i)
{
  if i == 0 {
    calc {
      BubbleSortBound(len, 0);
      == 0;
      == SumRange(0, len) - SumRange(0, len);
    }
  } else {
    BubbleSortBoundSum(len, i - 1);
    calc {
      BubbleSortBound(len, i);
      == BubbleSortBound(len, i - 1) + (len - i);
      == SumRange(0, len) - SumRange(0, len - (i - 1)) + (len - i);
      == SumRange(0, len) - SumRange(0, len - i + 1) + (len - i);
      == SumRange(0, len) - (SumRange(0, len - i) + (len - i)) + (len - i);
      == SumRange(0, len) - SumRange(0, len - i);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method BubbleSort(a: array<int>) returns (n: nat) 
  modifies a
  ensures n <= NChoose2(a.Length)
// </vc-spec>
// <vc-code>
{
  n := 0;
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant n == SumRange(0, a.Length) - SumRange(0, a.Length - i)
  {
    var j := 0;
    while j < a.Length - 1 - i
      invariant 0 <= j <= a.Length - 1 - i
      invariant n == SumRange(0, a.Length) - SumRange(0, a.Length - i) + j
    {
      if a[j] > a[j + 1] {
        a[j], a[j + 1] := a[j + 1], a[j];
      }
      n := n + 1;
      j := j + 1;
    }
    i := i + 1;
  }
  BubbleSortBoundCorrect(a.Length);
}
// </vc-code>