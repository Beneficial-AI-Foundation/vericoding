

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
  ghost var oldSeq: seq<nat> := s[..];
  var i := 0;
  while i < s.Length
    invariant 0 <= i <= s.Length
    invariant forall j :: 0 <= j < i ==>
      if oldSeq[j] % 2 == 1 then s[j] == oldSeq[j] + 1 else s[j] == oldSeq[j]
    invariant forall j :: i <= j < s.Length ==> s[j] == oldSeq[j]
    decreases s.Length - i
  {
    var x := s[i];
    if x % 2 == 1 {
      s[i] := x + 1;
    } else {
      s[i] := x;
    }
    i := i + 1;
  }
}
// </vc-code>

