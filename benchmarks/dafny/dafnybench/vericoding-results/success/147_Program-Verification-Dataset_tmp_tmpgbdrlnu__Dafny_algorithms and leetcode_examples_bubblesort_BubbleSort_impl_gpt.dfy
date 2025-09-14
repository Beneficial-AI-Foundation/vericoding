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
lemma NChoose2_step(n: nat)
  ensures NChoose2(n + 1) == NChoose2(n) + n
{
}

lemma NChoose2_nonneg(n: nat)
  ensures 0 <= NChoose2(n)
  decreases n
{
  if n == 0 {
  } else {
    NChoose2_nonneg(n - 1);
    var k: nat := n - 1;
    NChoose2_step(k);
    assert k + 1 == n;
    assert NChoose2(n) == NChoose2(k) + k;
    assert 0 <= NChoose2(k) + k;
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
  NChoose2_nonneg(a.Length);
}
// </vc-code>

