// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method common(l1 : seq<int>, l2 : seq<int>) returns (c : set<int>)

    ensures forall i :: i in c ==> i in l1 && i in l2
    ensures forall i :: i in l1 && i in l2 ==> i in c
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): fixed compilation error in invariant by using set intersection */
  var l2_set := set x | x in l2;
  c := {};
  var i := 0;
  while i < |l1|
    invariant 0 <= i <= |l1|
    invariant c == (set x | x in l1[..i]) * l2_set
  {
    if l1[i] in l2_set {
      c := c + {l1[i]};
    }
    i := i + 1;
  }
}
// </vc-code>
