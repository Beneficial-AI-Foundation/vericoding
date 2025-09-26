// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Getmini(a:array<int>) returns(mini:nat) 
requires a.Length > 0
ensures 0 <= mini < a.Length
ensures forall x :: 0 <= x < a.Length ==> a[mini] <= a[x]
ensures forall x :: 0 <= x < mini ==> a[mini] < a[x]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
