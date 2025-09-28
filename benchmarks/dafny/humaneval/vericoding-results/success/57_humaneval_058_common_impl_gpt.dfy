// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): define intersection via bounded index comprehension to ensure finiteness */
function intersection(l1: seq<int>, l2: seq<int>): set<int>
{
  set i:int | 0 <= i < |l1| && l1[i] in l2 :: l1[i]
}
// </vc-helpers>

// <vc-spec>
method common(l1 : seq<int>, l2 : seq<int>) returns (c : set<int>)

    ensures forall i :: i in c ==> i in l1 && i in l2
    ensures forall i :: i in l1 && i in l2 ==> i in c
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): compute intersection using bounded comprehension helper */
  c := intersection(l1, l2);
}
// </vc-code>
