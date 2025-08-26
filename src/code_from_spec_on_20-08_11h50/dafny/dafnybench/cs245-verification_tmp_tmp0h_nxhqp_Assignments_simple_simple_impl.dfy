method simple(y: int) returns (x: int) 
  requires y==6;
  ensures x==7;
// </vc-spec>
// <vc-code>
{
  x := y + 1;
}
// </vc-code>

/* Proof of implied (a): 
    Let y = 6.
    Then add 1 to both sides of the equality: y + 1 = 6 + 1
    Then y + 1 = 7.
*/