//https://stackoverflow.com/questions/69364687/how-to-prove-time-complexity-of-bubble-sort-using-dafny
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

// <vc-helpers>
lemma SumRangeFormula(n: int)
  requires n >= 0
  ensures SumRange(0, n) == NChoose2(n)
{
  if n <= 1 {
    // Base cases
  } else {
    SumRangeFormula(n - 1);
    assert SumRange(0, n) == SumRange(0, n - 1) + (n - 1);
    assert SumRange(0, n - 1) == NChoose2(n - 1);
    assert NChoose2(n - 1) == (n - 1) * (n - 2) / 2;
    assert SumRange(0, n) == (n - 1) * (n - 2) / 2 + (n - 1);
    // Fix arithmetic reasoning
    calc {
      (n - 1) * (n - 2) / 2 + (n - 1);
      == 
      (n - 1) * (n - 2) / 2 + (n - 1) * 2 / 2;
      == 
      ((n - 1) * (n - 2) + (n - 1) * 2) / 2;
      == 
      (n - 1) * ((n - 2) + 2) / 2;
      == 
      (n - 1) * n / 2;
    }
    assert SumRange(0, n) == NChoose2(n);
  }
}

lemma SumRangeAdditive(lo: int, mid: int, hi: int)
  requires lo <= mid <= hi
  ensures SumRange(lo, hi) == SumRange(lo, mid) + SumRange(mid, hi)
  decreases hi - lo
{
  if lo >= hi {
    // Base case
  } else if mid == hi {
    // SumRange(mid, hi) == 0
  } else {
    SumRangeAdditive(lo, mid, hi - 1);
    assert SumRange(lo, hi) == SumRange(lo, hi - 1) + (hi - 1);
    assert SumRange(lo, hi - 1) == SumRange(lo, mid) + SumRange(mid, hi - 1);
    assert SumRange(mid, hi) == SumRange(mid, hi - 1) + (hi - 1);
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method BubbleSort(a: array<int>) returns (n: nat) 
  modifies a
  ensures n <= NChoose2(a.Length)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  n := 0;
  var i := 0;
  
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant n <= SumRange(0, i)
  {
    var j := 0;
    while j < a.Length - 1 - i
      invariant 0 <= j <= a.Length - 1 - i
      invariant n <= SumRange(0, i) + j
    {
      if a[j] > a[j + 1] {
        a[j], a[j + 1] := a[j + 1], a[j];
      }
      n := n + 1;
      j := j + 1;
    }
    
    assert n <= SumRange(0, i) + (a.Length - 1 - i);
    SumRangeAdditive(0, i, i + 1);
    assert SumRange(0, i + 1) == SumRange(0, i) + SumRange(i, i + 1);
    assert SumRange(i, i + 1) == i;
    assert SumRange(0, i + 1) == SumRange(0, i) + i;
    // Since i < a.Length, we have 2*i < a.Length + i - 1, so a.Length - 1 - i < i when a.Length > 1
    // For the general case, we need to show a.Length - 1 - i <= i
    if a.Length >= 1 {
      assert 2 * i < a.Length + i - 1;
      assert a.Length - 1 - i < i + 1;
    }
    if a.Length - 1 - i <= i {
      assert SumRange(0, i) + (a.Length - 1 - i) <= SumRange(0, i) + i;
    } else {
      // If a.Length - 1 - i > i, we can still bound n appropriately
      assert n <= SumRange(0, i) + (a.Length - 1 - i);
    }
    assert SumRange(0, i) + i == SumRange(0, i + 1);
    
    i := i + 1;
  }
  
  SumRangeFormula(a.Length);
  assert n <= SumRange(0, a.Length);
  assert SumRange(0, a.Length) == NChoose2(a.Length);
}
// </vc-code>
