// <vc-helpers>
// </vc-helpers>

// <vc-description>
/*
function_signature: def choose_num(x: int, y: int) -> int
This function takes two positive numbers x and y and returns the biggest even integer number that is in the range [x, y] inclusive. If there's no such number, then the function should return -1.
*/
// </vc-description>

// <vc-spec>
method choose_num(x: int, y: int) returns (result: int)
  requires x > 0 && y > 0
  ensures result == -1 ==> (forall i :: x <= i <= y ==> i % 2 == 1)
  ensures result != -1 ==> (x <= result <= y && result % 2 == 0 && 
                           forall i :: x <= i <= y && i % 2 == 0 ==> i <= result)
// </vc-spec>
// <vc-code>
{
  if x > y {
    return -1;
  }
  
  var i := y;
  while i >= x
    invariant i < x ==> (forall j :: x <= j <= y ==> j % 2 == 1)
    invariant i >= x ==> (forall j :: i < j <= y && j % 2 == 0 ==> j <= y)
  {
    if i % 2 == 0 {
      return i;
    }
    i := i - 1;
  }
  
  return -1;
}
// </vc-code>
