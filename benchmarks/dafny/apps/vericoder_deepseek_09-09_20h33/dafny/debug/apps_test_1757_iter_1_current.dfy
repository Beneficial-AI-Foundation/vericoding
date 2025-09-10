function isFibonacci(num: int): bool
  requires num >= 1
{
  isFibHelper(num, 1, 1)
}

function isFibHelper(num: int, prev: int, curr: int): bool
  requires num >= 1 && prev >= 1 && curr >= 1
  decreases if curr >= num then 0 else num - curr
{
  if curr == num then true
  else if curr > num then false
  else isFibHelper(num, curr, prev + curr)
}

// <vc-helpers>
lemma fibIndexProperty() 
  ensures isFibonacci(1) && isFibonacci(2)
  ensures forall i :: i >= 1 && isFibonacci(i) ==> (exists k :: i == fib(k) && k >= 1)
{
  // Proof that 1 and 2 are Fibonacci numbers
  assert isFibHelper(1, 1, 1) == true;
  assert isFibHelper(2, 1, 1) == true;
}

function fib(n: nat): nat
  decreases n
{
  if n == 0 then 0
  else if n == 1 then 1
  else fib(n-1) + fib(n-2)
}

lemma fibMonotonic() 
  ensures forall m, n :: m <= n ==> fib(m) <= fib(n)
  decreases 0
{
  // Fibonacci sequence is non-decreasing
}

predicate validFibPosition(i: int) 
  requires 1 <= i <= 1000
{
  isFibonacci(i)
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: string)
  requires n >= 1 && n <= 1000
  ensures |result| == n
  ensures forall i :: 0 <= i < |result| ==> result[i] == 'O' || result[i] == 'o'
  ensures forall i :: 1 <= i <= n ==> (isFibonacci(i) <==> result[i-1] == 'O')
  ensures forall i :: 1 <= i <= n ==> (!isFibonacci(i) <==> result[i-1] == 'o')
// </vc-spec>
// <vc-code>
{
  result := new char[n];
  var i := 0;
  while i < n 
    invariant 0 <= i <= n
    invariant |result| == n
    invariant forall j :: 0 <= j < i ==> result[j] == 'O' || result[j] == 'o'
    invariant forall j :: 1 <= j <= i+1 ==> (isFibonacci(j) <==> (if j-1 < i then result[j-1] == 'O' else true))
    invariant forall j :: 1 <= j <= i+1 ==> (!isFibonacci(j) <==> (if j-1 < i then result[j-1] == 'o' else true))
    decreases n - i
  {
    if isFibonacci(i+1) {
      result[i] := 'O';
    } else {
      result[i] := 'o';
    }
    i := i + 1;
  }
}
// </vc-code>

