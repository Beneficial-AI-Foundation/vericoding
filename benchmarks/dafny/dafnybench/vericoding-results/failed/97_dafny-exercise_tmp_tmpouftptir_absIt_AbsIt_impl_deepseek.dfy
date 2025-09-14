

// <vc-helpers>
// Helper function to capture old state
function fresh_ref(s: array<int>): seq<int>
ensures fresh_ref(s) == s[..]
{
  s[..]
}
// </vc-helpers>

// <vc-spec>
method AbsIt(s: array<int>) 
modifies s
ensures forall i :: 0 <= i < s.Length ==> if old(s[i]) < 0 then s[i] == -old(s[i]) else s[i] == old(s[i])
ensures s.Length == old(s).Length
// </vc-spec>
// <vc-code>
{
  var index := 0;
  ghost var old_s := fresh_ref(s);
  while index < s.Length
    invariant 0 <= index <= s.Length
    invariant forall i :: 0 <= i < index ==> 
      if old_s[i] < 0 then s[i] == -old_s[i] else s[i] == old_s[i]
    invariant s.Length == old_s.Length
  {
    if s[index] < 0 {
      s[index] := -s[index];
    }
    index := index + 1;
  }
}
// </vc-code>

