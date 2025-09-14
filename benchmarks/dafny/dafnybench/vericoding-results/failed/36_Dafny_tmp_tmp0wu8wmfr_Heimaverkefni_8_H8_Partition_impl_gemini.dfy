// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Partition( m: multiset<int> )
        returns( pre: multiset<int>, p: int, post: multiset<int> )
    requires |m| > 0;
    ensures p in m;
    ensures m == pre+multiset{p}+post;
     ensures forall z | z in pre :: z <= p;
     ensures forall z | z in post :: z >= p;
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Changed partitioning condition from x < p to x <= p. */
{
  p :| p in m;
  var m_rest := m - multiset{p};
  pre := multiset{};
  post := multiset{};
  while m_rest != multiset{}
    invariant m == pre + post + multiset{p} + m_rest
    invariant forall z | z in pre :: z <= p
    invariant forall z | z in post :: z > p
    decreases |m_rest|
  {
    var x :| x in m_rest;
    m_rest := m_rest - multiset{x};
    if x <= p {
      pre := pre + multiset{x};
    } else {
      post := post + multiset{x};
    }
  }
}
// </vc-code>
