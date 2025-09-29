// <vc-preamble>
function NChoose2(n: int): int
{
  n * (n - 1) / 2
}

function SumRange(lo: int, hi: int): int
  decreases hi - lo
{
  if lo >= hi then 0
  else SumRange(lo, hi - 1) + hi - 1
}
// </vc-preamble>

// <vc-helpers>
lemma NChoose2Lemma(k: int)
  requires k >= 1
  ensures NChoose2(k) - NChoose2(k - 1) == k - 1
{}
// </vc-helpers>

// <vc-spec>
method BubbleSort(a: array<int>) returns (n: nat) 
  modifies a
  ensures n <= NChoose2(a.Length)
// </vc-spec>
// <vc-code>
{
  n := 0;
  var len := a.Length;
  var i := 0;
  while i < len
    invariant 0 <= i <= len
    invariant n <= NChoose2(len) - NChoose2(len - i)
    decreases len - i
  {
    var n_before_inner := n;
    var j := 0;
    while j < len - 1 - i
      invariant 0 <= j <= len - 1 - i
      invariant n <= n_before_inner + j
      decreases len - 1 - i - j
    {
      if a[j] > a[j+1] {
        a[j], a[j+1] := a[j+1], a[j];
        n := n + 1;
      }
      j := j + 1;
    }
    if len - i >= 1 {
      NChoose2Lemma(len - i);
    } 
    i := i + 1;
  }
}
// </vc-code>
