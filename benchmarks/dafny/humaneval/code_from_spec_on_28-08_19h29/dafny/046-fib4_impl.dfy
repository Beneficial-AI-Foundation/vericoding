function fib4_rec(n: nat): nat
  decreases n
{
  if n == 0 || n == 1 || n == 2 then 0
  else if n == 3 then 1
  else fib4_rec(n - 1) + fib4_rec(n - 2) + fib4_rec(n - 3) + fib4_rec(n - 4)
}

// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-description>
/*
function_signature: def fib4(n: int)
The Fib4 number sequence is a sequence similar to the Fibbonacci sequnece that's defined as follows: fib4(0) -> 0 fib4(1) -> 0 fib4(2) -> 2 fib4(3) -> 0 fib4(n) -> fib4(n-1) + fib4(n-2) + fib4(n-3) + fib4(n-4). Please write a function to efficiently compute the n-th element of the fib4 number sequence.  Do not use recursion.
*/
// </vc-description>

// <vc-spec>
method fib4(n: int) returns (result: int)
  requires n >= 0
  ensures result == fib4_rec(n)
// </vc-spec>
// <vc-code>
{
  if n == 0 || n == 1 || n == 2 {
    return 0;
  } else if n == 3 {
    return 1;
  }
  
  var f0 := 0;
  var f1 := 0;
  var f2 := 0;
  var f3 := 1;
  var i := 4;
  
  while i <= n
    invariant 0 <= i <= n + 1
    invariant i >= 4 ==> fib4_rec(i - 4) == f0
    invariant i >= 3 ==> fib4_rec(i - 3) == f1
    invariant i >= 2 ==> fib4_rec(i - 2) == f2
    invariant i >= 1 ==> fib4_rec(i - 1) == f3
    decreases n - i
  {
    var next := f0 + f1 + f2 + f3;
    f0 := f1;
    f1 := f2;
    f2 := f3;
    f3 := next;
    i := i + 1;
  }
  return f3;
}
// </vc-code>
