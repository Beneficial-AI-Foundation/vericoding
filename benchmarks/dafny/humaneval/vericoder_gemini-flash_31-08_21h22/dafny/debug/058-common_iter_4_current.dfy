

// <vc-helpers>
lemma lemma_append_singleton(s: set<int>, x: int)
  ensures forall e :: e in (s + {x}) <==> (e in s || e == x)
{}
// </vc-helpers>

// <vc-spec>
method common(l1 : seq<int>, l2 : seq<int>) returns (c : set<int>)
   // post-conditions-start
    ensures forall i :: i in c ==> i in l1 && i in l2
    ensures forall i :: i in l1 && i in l2 ==> i in c
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var s := {};
  for i := 0 to |l1|
    invariant 0 <= i <= |l1|
    invariant forall x :: x in s ==> x in l1[..i] && x in l2
    invariant forall x :: x in l1[..i] && x in l2 ==> x in s
  {
    if i < |l1| { // Add this check to prevent out-of-bounds access
        if l1[i] in l2
        {
            s := s + {l1[i]};
            lemma_append_singleton(s - {l1[i]}, l1[i]); // Apply the lemma here
        }
    }
  }
  return s;
}
// </vc-code>

