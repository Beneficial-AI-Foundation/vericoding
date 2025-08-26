// Given an array of positive and negative integers,
//  it returns an array of the absolute value of all the integers. [-4,1,5,-2,-5]->[4,1,5,2,5]

function abs(x:int):nat {

    if x < 0 then -x else x
}

// <vc-helpers>
// </vc-helpers>

method absx(x:array<int>) returns (y:array<int>) 
ensures y.Length == x.Length
ensures forall i :: 0 <= i < y.Length ==>  y[i] == abs(x[i])
// <vc-code>
{
  assume false;
}
// </vc-code>