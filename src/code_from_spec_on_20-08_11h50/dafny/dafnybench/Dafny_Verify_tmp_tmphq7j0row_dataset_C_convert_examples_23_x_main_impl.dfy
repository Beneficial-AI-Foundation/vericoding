method main(n: int) returns (sum: int, i: int)
requires n >= 0
// </vc-spec>
// <vc-code>
{
  sum := 0;
  i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant sum >= 0
  {
    sum := sum + i;
    i := i + 1;
  }
  
  assert sum >= 0;
}
// </vc-code>

// MODULE main
//  int i;
//  int sum;
//  int n;

//  assume(sum == 0);
//  assume(n >= 0);
//  assume(i == 0);

//  while(i < n){
//      sum = sum + i;
//      i = i + 1;
//  }

//  assert(sum >= 0);   

// END MODULE