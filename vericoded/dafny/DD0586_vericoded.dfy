

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
  var i := 0;
  while i < s.Length
    invariant 0 <= i <= s.Length
    invariant forall j :: 0 <= j < i ==> 
                    if old(s[j]) % 2 == 1 then s[j] == old(s[j]) + 1
                    else s[j] == old(s[j])
    invariant forall j :: i <= j < s.Length ==> s[j] == old(s[j])
  {
    if s[i] % 2 == 1 {
      s[i] := s[i] + 1;
    }
    i := i + 1;
  }
}
// </vc-code>

