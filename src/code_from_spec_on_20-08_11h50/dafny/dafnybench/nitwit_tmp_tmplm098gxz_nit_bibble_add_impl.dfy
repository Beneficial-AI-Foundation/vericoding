function nit_add(b: nat, x: nat, y: nat): (nat, nat)
  requires b >= 2
  requires x < b && y < b
  ensures nit_add(b, x, y).0 < b
  ensures nit_add(b, x, y).1 < b
{
  var sum := x + y;
  (sum % b, sum / b)
}

function nit_add_three(b: nat, carry: nat, x: nat, y: nat): (nat, nat)
  requires b >= 2
  requires carry < b && x < b && y < b
  ensures nit_add_three(b, carry, x, y).0 < b
  ensures nit_add_three(b, carry, x, y).1 < b
{
  var sum := carry + x + y;
  (sum % b, sum / b)
}

method bibble_add(b: nat, p: seq<nat>, q: seq<nat>) returns (r: seq<nat>)
  requires b >= 2
  requires |p| == 4 && |q| == 4
  requires forall i :: 0 <= i < 4 ==> p[i] < b && q[i] < b
  ensures |r| == 4
  ensures forall i :: 0 <= i < 4 ==> r[i] < b
{
  var carry := 0;
  var digit0, digit1, digit2, digit3 : nat;
  
  // Add rightmost nits (index 3)
  var temp3 := nit_add(b, p[3], q[3]);
  digit3 := temp3.0;
  carry := temp3.1;
  
  // Add next nits with carry (index 2)
  var temp2 := nit_add_three(b, carry, p[2], q[2]);
  digit2 := temp2.0;
  carry := temp2.1;
  
  // Add next nits with carry (index 1)
  var temp1 := nit_add_three(b, carry, p[1], q[1]);
  digit1 := temp1.0;
  carry := temp1.1;
  
  // Add leftmost nits with carry (index 0)
  var temp0 := nit_add_three(b, carry, p[0], q[0]);
  digit0 := temp0.0;
  carry := temp0.1;
  
  // The final carry is discarded (overflow beyond 4 nits)
  r := [digit0, digit1, digit2, digit3];
}