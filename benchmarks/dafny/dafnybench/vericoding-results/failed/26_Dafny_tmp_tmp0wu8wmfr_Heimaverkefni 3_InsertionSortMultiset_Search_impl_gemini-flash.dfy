// Höfundur spurningar:  Snorri Agnarsson, snorri@hi.is
// Permalink spurningar: https://rise4fun.com/Dafny/G4sc3

// Höfundur lausnar:     Alexander Guðmundsson
// Permalink lausnar:    https://rise4fun.com/Dafny/nujsu

// Insertion sort með hjálp helmingunarleitar.

// <vc-helpers>
function Search'Helper(s: seq<int>, x: int, low: int, high: int): (k: int)
  requires 0 <= low <= high + 1
  requires high <= |s|
  requires forall p, q | 0 <= p < q < |s| :: s[p] <= s[q]
  ensures low <= k <= high + 1
  ensures forall i | low <= i < k && i < |s| :: s[i] < x
  ensures forall i | k <= i < high + 1 && i < |s| :: s[i] >= x
{
  if low > high then
    low
  else
    var mid := (low + high) / 2;
    if s[mid] < x then
      Search'Helper(s, x, mid + 1, high)
    else if s[mid] > x then
      Search'Helper(s, x, low, mid - 1)
    else
      // s[mid] == x
      // Find the first occurrence of s[mid] == x
      var i := mid;
      while i > low && s[i-1] == x
        decreases i
        invariant low <= i <= mid + 1
        invariant s[i] == x
      {
        i := i - 1;
      }
      i
}
// </vc-helpers>

// <vc-spec>
method Search( s: seq<int>, x: int ) returns ( k: int )
    // Ekki má breyta forskilyrðum eða eftirskilyrðum fallsins
    requires forall p,q | 0 <= p < q < |s| :: s[p] <= s[q];
    ensures 0 <= k <= |s|;
    ensures forall i | 0 <= i < k :: s[i] <= x;
    ensures forall i | k <= i < |s| :: s[i] >= x;
    ensures forall z | z in s[..k] :: z <= x;
    ensures forall z | z in s[k..] :: z >= x;
    ensures s == s[..k]+s[k..];
// </vc-spec>
// <vc-code>
{
  var k := Search'Helper(s, x, 0, |s|-1);
  return k;
}
// </vc-code>

