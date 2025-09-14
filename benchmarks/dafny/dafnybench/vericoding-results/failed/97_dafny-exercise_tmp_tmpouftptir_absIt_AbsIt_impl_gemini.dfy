// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No changes from previous iteration. */
function abs(x: int): int { if x < 0 then -x else x }
// </vc-helpers>

// <vc-spec>
method AbsIt(s: array<int>) 
modifies s
ensures forall i :: 0 <= i < s.Length ==> if old(s[i]) < 0 then s[i] == -old(s[i]) else s[i] == old(s[i])
ensures s.Length == old(s).Length
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Changed from while loop to forall statement to be more declarative. */
{
  forall i | 0 <= i < s.Length
    modifies s[i]
  {
    s[i] := abs(s[i]);
  }
}
// </vc-code>
