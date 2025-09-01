function tri(n: nat): nat
  decreases if n % 2 == 0 then 0 else n
{
  if n == 1 then 3
  else if n % 2 == 0 then 1 + n / 2
  else tri(n - 1) + tri(n - 2) + tri(n + 1)
}

// <vc-helpers>
lemma tri_odd_helper(n: nat)
  requires n % 2 != 0 && n >= 3
  ensures tri(n) == tri(n-1) + tri(n-2) + tri(n+1)
{
  reveal tri();
}

lemma tri_even_property(n: nat)
  requires n % 2 == 0
  ensures tri(n) == 1 + n / 2
{
  reveal tri();
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
  var a := new nat[n+1];
  for i := 0 to n+1
    invariant forall j :: 0 <= j < i ==> a[j] == tri(j)
  {
    if i % 2 == 0 {
      a[i] := 1 + i / 2;
    } else {
      if i == 1 {
        a[i] := 3;
      } else {
        calc {
          tri(i);
          == { tri_odd_helper(i); }
          tri(i-1) + tri(i-2) + tri(i+1);
          == { tri_even_property(i+1); }
          tri(i-1) + tri(i-2) + (1 + (i+1)/2);
          == 
          a[i-1] + a[i-2] + (1 + (i+1)/2);
        }
        a[i] := a[i-1] + a[i-2] + (1 + (i+1)/2);
      }
    }
  }
  return a[..];
}
// </vc-code>

