// Predicates for validity
predicate valid_base(b: nat) { b >= 2 }
predicate nitness(b: nat, x: nat) { x < b }
predicate bibbleness(b: nat, p: array<nat>) 
  requires p.Length == 4
  reads p
{ forall i :: 0 <= i < 4 ==> nitness(b, p[i]) }

// <vc-spec>
method nit_bibble_increment(b: nat, p: array<nat>) returns (r: array<nat>)
  requires valid_base(b)
  requires p.Length == 4
  requires bibbleness(b, p)
  ensures r.Length == 4
  ensures bibbleness(b, r)
  ensures fresh(r)
// </vc-spec>

// <vc-helpers>
method nit_add_general(b: nat, x: nat, y: nat, carry_in: nat) returns (result: nat, carry_out: nat)
  requires valid_base(b)
  requires nitness(b, x)
  requires nitness(b, y) 
  requires nitness(b, carry_in)
  ensures nitness(b, result)
  ensures carry_out == 0 || carry_out == 1
{
  var temp := x + y + carry_in;
  result := temp % b;
  carry_out := temp / b;
}
// </vc-helpers>

// <vc-code>
{
  r := new nat[4];
  var carry := 1; // We're adding 1 to increment;
  var i := 3; // Start from rightmost nit;
  
  // Process each nit from right to left
  while i >= 0
    invariant -1 <= i <= 3
    invariant carry == 0 || carry == 1
    invariant forall j :: i + 1 <= j < 4 ==> nitness(b, r[j])
    decreases i + 1
  {
    var sum := p[i] + carry;
    r[i] := sum % b;
    carry := sum / b;
    i := i - 1;
  }
  
  // Verify all elements satisfy nitness
  assert forall j :: 0 <= j < 4 ==> nitness(b, r[j]);
}
// </vc-code>