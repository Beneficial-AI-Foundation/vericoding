// SPEC

//Problem02
//As you can see below, Dafny claims that after executing the following method
//strange() we will have that 1=2;
method q(x:nat, y:nat) returns (z:nat)
requires y - x > 2
ensures x < z*z < y
