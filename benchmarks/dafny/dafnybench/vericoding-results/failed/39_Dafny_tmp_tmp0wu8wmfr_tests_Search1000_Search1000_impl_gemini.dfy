// <vc-preamble>
predicate Is2Pow( n: int )
    decreases n;
{
    if n < 1 then
        false
    else if n == 1 then
        true
    else
        n%2 == 0 && Is2Pow(n/2)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Search1000( a: array<int>, x: int ) returns ( k: int )
    requires a.Length >= 1000;
    requires forall p,q | 0 <= p < q < 1000 :: a[p] <= a[q];
    ensures 0 <= k <= 1000;
    ensures forall r | 0 <= r < k :: a[r] < x;
    ensures forall r | k <= r < 1000 :: a[r] >= x;
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Switched invariant style to match spec, as previous correct logic failed due to style warnings in surrounding code. */
  var low := 0;
  var high := 1000;
  while low < high
    invariant 0 <= low <= high <= 1000
    invariant forall r | 0 <= r < low :: a[r] < x
    invariant forall r | high <= r < 1000 :: a[r] >= x
    decreases high - low
  {
    var mid := low + (high - low) / 2;
    if a[mid] < x {
      low := mid + 1;
    } else {
      high := mid;
    }
  }
  k := low;
}
// </vc-code>
