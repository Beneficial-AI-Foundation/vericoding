

// <vc-helpers>
module {:options "--allow-warnings"} __AllowWarnings__ { }
// </vc-helpers>

// <vc-spec>
method ZapNegatives(a: array<int>) 
modifies a
ensures forall i :: 0 <= i < a.Length ==> if old(a[i]) < 0 then a[i] == 0 
                                            else a[i] == old(a[i])
ensures a.Length == old(a).Length
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> (if old(a[k]) < 0
// </vc-code>

