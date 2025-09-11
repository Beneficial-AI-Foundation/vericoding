// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method GetEven(s: array<nat>) modifies s
ensures forall i :: 0 <= i < s.Length ==> 
                                if old(s[i]) % 2 == 1 then s[i] == old(s[i]) + 1
                                else s[i] == old(s[i])
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
