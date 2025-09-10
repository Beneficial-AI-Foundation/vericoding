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
function isFibonacci_1(num: int): bool
  requires num >= 1
{
  isFibHelper_1(num, 1, 1)
}

function isFibHelper_1(num: int, prev: int, curr: int): bool
  requires num >= 1 && prev >= 1 && curr >= 1
  decreases if curr >= num then 0 else num - curr
{
  if curr == num then true
  else if curr > num then false
  else isFibHelper_1(num, curr, prev + curr)
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
    var resultString := new char[n];
    for i := 1 to n
      invariant 1 <= i <= n + 1
      invariant forall k :: 1 <= k < i ==> (isFibonacci_1(k) <==> resultString[k-1] == 'O')
      invariant forall k :: 1 <= k < i ==> (!isFibonacci_1(k) <==> resultString[k-1] == 'o')
    {
        if isFibonacci_1(i) {
            resultString[i-1] := 'O';
        } else {
            resultString[i-1] := 'o';
        }
    }
    return new String(resultString);
}
// </vc-code>

