class Rounding {
  var thresholds: array<int>

// <vc-spec>
  function Valid(): bool
    reads this, thresholds
  {
    forall m,n :: 0 <= m < n < thresholds.Length ==> thresholds[m] <= thresholds[n]
  }

// <vc-helpers>
// </vc-helpers>

method RoundDown(k: int) returns (r: int)
    requires Valid()
    ensures -1 <= r < thresholds.Length
    ensures forall m :: r < m < thresholds.Length ==> k < thresholds[m]
    ensures 0 <= r ==> thresholds[r] <= k
// </vc-spec>
// <vc-code>
{
  if thresholds.Length == 0 {
    r := -1;
    return;
  }
  
  var low := 0;
  var high := thresholds.Length;
  
  while low < high
    invariant 0 <= low <= high <= thresholds.Length
    invariant forall m :: 0 <= m < low ==> thresholds[m] <= k
    invariant forall m :: high <= m < thresholds.Length ==> k < thresholds[m]
    decreases high - low
  {
    var mid := (low + high) / 2;
    if thresholds[mid] <= k {
      low := mid + 1;
    } else {
      high := mid;
    }
  }
  
  r := low - 1;
}
// </vc-code>

}