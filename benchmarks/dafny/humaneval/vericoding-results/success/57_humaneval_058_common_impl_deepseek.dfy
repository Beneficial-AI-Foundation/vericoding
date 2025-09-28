// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function inSeq(x: int, s: seq<int>): bool
  {
    exists i | 0 <= i < |s| :: s[i] == x
  }

/* helper modified by LLM (iteration 3): simplified helpers to use inSeq */
// </vc-helpers>

// <vc-spec>
method common(l1 : seq<int>, l2 : seq<int>) returns (c : set<int>)

    ensures forall i :: i in c ==> i in l1 && i in l2
    ensures forall i :: i in l1 && i in l2 ==> i in c
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): simplified implementation using sets */
  c := {};
  var index := 0;
  
  while index < |l1|
    invariant 0 <= index <= |l1|
    invariant forall i :: i in c ==> i in l1 && i in l2
    invariant forall x :: x in l1[..index] && x in l2 ==> x in c
  {
    if l1[index] in l2 {
      c := c + {l1[index]};
    }
    index := index + 1;
  }
}
// </vc-code>
