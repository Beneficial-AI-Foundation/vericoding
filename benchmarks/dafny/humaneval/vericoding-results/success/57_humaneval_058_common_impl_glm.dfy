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
  /* code modified by LLM (iteration 2): fixed set comprehension syntax */
  c := set i | i in l1 && i in l2;
}
// </vc-code>
