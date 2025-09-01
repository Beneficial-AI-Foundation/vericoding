function tri(n: nat): nat
  decreases if n % 2 == 0 then 0 else n
{
  if n == 1 then 3
  else if n % 2 == 0 then 1 + n / 2
  else tri(n - 1) + tri(n - 2) + tri(n + 1)
}

// <vc-helpers>
function tri(n: nat): nat
  decreases if n % 2 == 0 then 0 else n
{
  if n == 0 then 1
  else if n == 1 then 3
  else if n % 2 == 0 then 1 + n / 2
  else tri(n - 1) + tri(n - 2) + tri(n + 1)
}
// </vc-helpers>

// <vc-spec>
method Tribonacci(n: nat) returns (result: seq<nat>)
  // post-conditions-start
  ensures |result| == n + 1
  ensures forall i :: 0 <= i <= n ==> result[i] == tri(i)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var res: seq<nat> := [];
  for i := 0 to n
    invariant |res| == i
    invariant forall j :: 0 <= j < i ==> res[j] == tri(j)
  {
    var val: nat;
    if i == 0 {
      val := 1;
    } else if i == 1 {
      val := 3;
    } else if i % 2 == 0 {
      val := 1 + i / 2;
    } else {
      val := res[i-1] + res[i-2] + (1 + (i+1)/2);
    }
    res := res + [val];
  }
  result := res;
}
// </vc-code>

