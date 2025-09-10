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
  
  // Prove that any Fibonacci number equals fib(k) for some k
  forall i | i >= 1 && isFibonacci(i)
    ensures exists k :: i == fib(k) && k >= 1
  {
    var k := 1;
    while fib(k) < i
      invariant k >= 1
      invariant fib(k) <= i
    {
      k := k + 1;
    }
    assert fib(k) == i;
  }
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
  // Prove fib is monotonic by induction
  forall m, n | m <= n
    ensures fib(m) <= fib(n)
  {
    if n == m {
      // Base case: m == n
    } else {
      // fib(n) = fib(n-1) + fib(n-2) >= fib(n-1) >= ... >= fib(m)
      fibMonotonic();
      assert fib(n-1) >= fib(m);
      assert fib(n) >= fib(n-1);
    }
  }
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
  var arr := new char[n];
  var i := 0;
  while i < n 
    invariant 0 <= i <= n
    invariant arr.Length == n
    invariant forall j :: 0 <= j < i ==> arr[j] == 'O' || arr[j] == 'o'
    invariant forall j :: 1 <= j <= i ==> (isFibonacci(j) <==> arr[j-1] == 'O')
    invariant forall j :: 1 <= j <= i ==> (!isFibonacci(j) <==> arr[j-1] == 'o')
    decreases n - i
  {
    if isFibonacci(i+1) {
      arr[i] := 'O';
    } else {
      arr[i] := 'o';
    }
    i := i + 1;
  }
  result := arr[..];
}
// </vc-code>

