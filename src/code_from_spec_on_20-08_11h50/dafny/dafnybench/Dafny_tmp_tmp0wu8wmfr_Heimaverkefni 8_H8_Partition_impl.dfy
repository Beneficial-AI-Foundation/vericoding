method Partition( m: multiset<int> )
        returns( pre: multiset<int>, p: int, post: multiset<int> )
    requires |m| > 0;
    ensures p in m;
    ensures m == pre+multiset{p}+post;
     ensures forall z | z in pre :: z <= p;
     ensures forall z | z in post :: z >= p;
// </vc-spec>
// <vc-code>
{
  // Choose p as any element from m
  var elements := m;
  p :| p in elements;
  
  // Initialize pre and post as empty multisets
  pre := multiset{};
  post := multiset{};
  
  // Remove p from elements since we've already selected it
  elements := elements - multiset{p};
  
  // Partition the remaining elements
  while elements != multiset{}
    invariant m == pre + multiset{p} + post + elements;
    invariant forall z | z in pre :: z <= p;
    invariant forall z | z in post :: z >= p;
    decreases |elements|;
  {
    var x :| x in elements;
    elements := elements - multiset{x};
    
    if x <= p {
      pre := pre + multiset{x};
    } else {
      post := post + multiset{x};
    }
  }
}
// </vc-code>