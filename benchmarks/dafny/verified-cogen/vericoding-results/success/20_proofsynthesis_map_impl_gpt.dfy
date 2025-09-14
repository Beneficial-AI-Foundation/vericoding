// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function inc4(n: int): int { n + 4 }
predicate BelowMaxMinus4(n: int) { n <= 0x7FFF_FFFB }
lemma Add4WithinInt32(n: int)
  requires BelowMaxMinus4(n)
  ensures n + 4 <= 0x7FFF_FFFF
{ }
// </vc-helpers>

// <vc-spec>
method myfun2(x: array<int>) 
    requires 
        forall k:int :: 0 <= k < x.Length ==> x[k] <= 0x7FFF_FFFB
    ensures 
        forall k:int :: 0 <= k < x.Length ==> x[k] == old(x[k]) + 4
    modifies x
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < x.Length
    invariant 0 <= i <= x.Length
    invariant forall k:int :: 0 <= k < i ==> x[k] == old(x[k]) + 4
    invariant forall k:int :: i <= k < x.Length ==> x[k] == old(x[k])
    decreases x.Length - i
  {
    x[i] := inc4(x[i]);
    i := i + 1;
  }
}
// </vc-code>
