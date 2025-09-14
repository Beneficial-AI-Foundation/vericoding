

// <vc-helpers>
lemma EvenLemma(x: nat)
ensures (x % 2 == 1 ==> (x + 1) % 2 == 0) && (x % 2 == 0 ==> x % 2 == 0)
{
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method GetEven(s: array<nat>) modifies s
ensures forall i :: 0 <= i < s.Length ==> 
                                if old(s[i]) % 2 == 1 then s[i] == old(s[i]) + 1
                                else s[i] == old(s[i])
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < s.Length
    invariant 0 <= i <= s.Length
    invariant forall j :: 0 <= j < s.Length ==> 
                        if old(s[j]) % 2 == 1 then (j < i ==> s[j] == old(s[j]) + 1) && (j >= i ==> s[j] == old(s[j]))
                        else s[j] == old(s[j])
  {
    if s[i] % 2 == 1 {
      s[i] := s[i] + 1;
    }
    i := i + 1;
  }
}
// </vc-code>

