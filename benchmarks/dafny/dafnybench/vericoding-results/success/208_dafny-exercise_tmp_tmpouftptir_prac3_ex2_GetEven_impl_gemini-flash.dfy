

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
    invariant forall k :: 0 <= k < i ==> 
                                if old(s[k]) % 2 == 1 then s[k] == old(s[k]) + 1
                                else s[k] == old(s[k])
    invariant forall k :: i <= k < s.Length ==> s[k] == old(s[k])
  {
    if s[i] % 2 == 1 {
      s[i] := s[i] + 1;
    }
    i := i + 1;
  }
}
// </vc-code>

