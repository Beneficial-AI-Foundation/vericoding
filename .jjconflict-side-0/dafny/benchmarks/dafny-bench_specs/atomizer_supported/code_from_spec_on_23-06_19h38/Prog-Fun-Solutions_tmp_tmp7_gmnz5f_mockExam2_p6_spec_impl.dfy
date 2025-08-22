//ATOM 
// problem 6:
// name:      Gabriele Berardi
// s-number: s4878728
// table:     XXXXX

ghost function f(n: int): int {
  if n <= 0 then 1 else n + f(n-1)*f(n-2)
}


//ATOM 

ghost function fSum(n: nat): int {
 // give the body of this function
  // it should return Sum(i: 0<=i < n: f(i))
  if n <= 0 then 0 else f(n-1) + fSum(n-1)
}


//IMPL problem6

method problem6(n:nat) returns (a: int)
ensures a == fSum(n)
{
  if n == 0 {
    a := 0;
    return;
  }
  
  var sum := 0;
  var i := 0;
  var prev2 := 1; // f(-1) = f(0) = 1
  var prev1 := 1; // f(0) = 1
  
  while i < n
    invariant 0 <= i <= n
    invariant sum == fSum(i)
    invariant i == 0 ==> (prev1 == f(0) && prev2 == f(-1))
    invariant i == 1 ==> (prev1 == f(0) && prev2 == f(-1))
    invariant i >= 2 ==> (prev1 == f(i-1) && prev2 == f(i-2))
  {
    var current: int;
    if i <= 0 {
      current := 1;
    } else {
      current := i + prev1 * prev2;
    }
    
    sum := sum + current;
    i := i + 1;
    
    prev2 := prev1;
    prev1 := current;
  }
  
  a := sum;
}