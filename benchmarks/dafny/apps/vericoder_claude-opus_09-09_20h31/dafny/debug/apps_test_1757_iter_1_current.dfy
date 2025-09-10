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
lemma FibonacciDecidable(num: int)
  requires num >= 1
  ensures isFibonacci(num) || !isFibonacci(num)
{
  // This is trivially true by the law of excluded middle
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
  result := "";
  var i := 1;
  
  while i <= n
    invariant 1 <= i <= n + 1
    invariant |result| == i - 1
    invariant forall j :: 0 <= j < |result| ==> result[j] == 'O' || result[j] == 'o'
    invariant forall j :: 1 <= j < i ==> (isFibonacci(j) <==> result[j-1] == 'O')
    invariant forall j :: 1 <= j < i ==> (!isFibonacci(j) <==> result[j-1] == 'o')
  {
    if isFibonacci(i) {
      result := result + "O";
    } else {
      result := result + "o";
    }
    i := i + 1;
  }
}
// </vc-code>

