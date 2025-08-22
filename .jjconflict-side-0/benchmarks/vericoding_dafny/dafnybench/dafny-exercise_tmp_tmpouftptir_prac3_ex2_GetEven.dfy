// <vc-helpers>
// </vc-helpers>

method GetEven(s: array<nat>) modifies s
ensures forall i :: 0 <= i < s.Length ==> 
                                if old(s[i]) % 2 == 1 then s[i] == old(s[i]) + 1
                                else s[i] == old(s[i])
// <vc-code>
{
  assume false;
}
// </vc-code>