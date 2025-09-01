function tri(n: nat): nat
  decreases if n % 2 == 0 then 0 else n
{
  if n == 1 then 3
  else if n % 2 == 0 then 1 + n / 2
  else tri(n - 1) + tri(n - 2) + tri(n + 1)
}

// <vc-helpers>

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
  var arr: array<nat>;
  if n == 0 {
    return [tri(0)];
  }
  arr := new nat[n + 1](_ => 0); // Initialize with default values

  arr[0] := tri(0);
  if n >= 1 {
    arr[1] := tri(1);
  }

  for i := 2 to n
    invariant 0 <= i <= n + 1
    invariant forall k :: 0 <= k < i ==> arr[k] == tri(k)
  {
    if i % 2 == 0 {
      arr[i] := 1 + i / 2;
    } else {
      arr[i] := arr[i - 1] + arr[i - 2] + tri(i + 1);
    }
  }

  return arr[..];
}
// </vc-code>

