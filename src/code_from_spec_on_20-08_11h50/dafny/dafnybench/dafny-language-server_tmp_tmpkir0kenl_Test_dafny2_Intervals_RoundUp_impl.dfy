// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The RoundDown and RoundUp methods in this file are the ones in the Boogie
// implementation Source/AbsInt/IntervalDomain.cs.

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

method RoundUp(k: int) returns (r: int)
    requires Valid()
    ensures 0 <= r <= thresholds.Length
    ensures forall m :: 0 <= m < r ==> thresholds[m] < k
    ensures r < thresholds.Length ==> k <= thresholds[r]
// </vc-spec>
// <vc-code>
{
  var lo := 0;
  var hi := thresholds.Length;
  
  while lo < hi
    invariant 0 <= lo <= hi <= thresholds.Length
    invariant forall m :: 0 <= m < lo ==> thresholds[m] < k
    invariant forall m :: hi <= m < thresholds.Length ==> k <= thresholds[m]
  {
    var mid := (lo + hi) / 2;
    
    if thresholds[mid] < k {
      lo := mid + 1;
    } else {
      hi := mid;
    }
  }
  
  r := lo;
}
// </vc-code>

}