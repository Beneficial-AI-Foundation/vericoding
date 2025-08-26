method q(x:nat, y:nat) returns (z:nat)
requires y - x > 2
ensures x < z*z < y

method strange()
ensures 1==2
{
  var x:nat := 4;
  var c := q(x, 2*x);
}