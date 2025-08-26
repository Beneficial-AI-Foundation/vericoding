method SearchLoop( a: seq<real>, i: int, j: int, x: real ) returns ( k: int )
    requires 0 <= i <= j <= |a|;
    requires forall p, q :: i <= p < q < j ==> a[p] >= a[q];
    ensures i <= k <= j;
    ensures forall r | i <= r < k :: a[r] >= x;
    ensures forall r | k <= r < j :: a[r] < x;
// </vc-spec>
// <vc-code>
{
  var left := i;
  var right := j;
  
  while left < right
    invariant i <= left <= right <= j
    invariant forall r | i <= r < left :: a[r] >= x
    invariant forall r | right <= r < j :: a[r] < x
  {
    var mid := (left + right) / 2;
    if a[mid] >= x {
      left := mid + 1;
    } else {
      right := mid;
    }
  }
  
  k := left;
}
// </vc-code>

// Ef eftirfarandi fall er ekki samþykkt þá eru
// föllin ekki að haga sér rétt að mati Dafny.