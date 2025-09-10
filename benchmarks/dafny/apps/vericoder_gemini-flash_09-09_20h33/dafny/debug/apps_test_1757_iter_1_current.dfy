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
function isFibonacci(num: int): bool
  requires num >= 1
{
  if num == 1 then true
  else isFibHelper(num, 1, 2)
}

function isFibHelper(num: int, prev: int, curr: int): bool
  requires num >= 1 && prev >= 1 && curr >= prev
  decreases if curr >= num then 0 else num - curr
{
  if curr == num then true
  else if curr > num then false
  else isFibHelper(num, curr, prev + curr)
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
        ensures forall k :: 1 <= k <= i ==> (isFibonacci(k) <==> resultString[k-1] == 'O')
        ensures forall k :: 1 <= k <= i ==> (!isFibonacci(k) <==> resultString[k-1] == 'o')
    {
        if isFibonacci(i) {
            resultString[i-1] := 'O';
        } else {
            resultString[i-1] := 'o';
        }
    }
    return new string(resultString);
}
// </vc-code>

