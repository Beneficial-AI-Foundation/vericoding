// <vc-preamble>
method Search( s: seq<int>, x: int ) returns ( k: int )

    requires forall p,q | 0 <= p < q < |s| :: s[p] <= s[q];
    ensures 0 <= k <= |s|;
    ensures forall i | 0 <= i < k :: s[i] <= x;
    ensures forall i | k <= i < |s| :: s[i] >= x;
    ensures forall z | z in s[..k] :: z <= x;
    ensures forall z | z in s[k..] :: z >= x;
    ensures s == s[..k]+s[k..];
{
  assume{:axiom} false;
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Sort( m: multiset<int> ) returns ( r: seq<int> )
    ensures multiset(r) == m;
    ensures forall p,q | 0 <= p < q < |r| :: r[p] <= r[q];
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): added decreases clause to ensure loop termination */
  r := [];
  var m_prime := m;
  while m_prime != multiset{}
    invariant multiset(r) + m_prime == m
    invariant forall p,q | 0 <= p < q < |r| :: r[p] <= r[q]
    decreases m_prime
  {
    var x :| x in m_prime;
    m_prime := m_prime - multiset{x};
    var k := Search(r, x);
    r := r[..k] + [x] + r[k..];
  }
}
// </vc-code>
