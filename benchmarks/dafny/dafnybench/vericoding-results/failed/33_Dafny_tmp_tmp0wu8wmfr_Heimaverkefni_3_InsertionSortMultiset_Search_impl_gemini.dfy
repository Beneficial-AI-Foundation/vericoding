// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Search( s: seq<int>, x: int ) returns ( k: int )

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
  /* code modified by LLM (iteration 5): added assertions to prove invariants */
  var low := 0;
  var high := |s|;

  while low < high
    invariant 0 <= low <= high <= |s|
    invariant forall i | 0 <= i < low :: s[i] <= x
    invariant forall i | high <= i < |s| :: s[i] >= x
  {
    var mid := low + (high - low) / 2;
    if s[mid] <= x {
      assert forall i :: low <= i <= mid ==> s[i] <= s[mid];
      low := mid + 1;
    } else {
      assert forall i :: mid <= i < high ==> s[mid] <= s[i];
      high := mid;
    }
  }

  k := low;
}
// </vc-code>
