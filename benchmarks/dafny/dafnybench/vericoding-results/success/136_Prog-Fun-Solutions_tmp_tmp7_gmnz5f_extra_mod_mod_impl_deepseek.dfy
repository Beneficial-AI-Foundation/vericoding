ghost function f(n: nat): nat {
    if n == 0 then 1 
    else if n%2 == 0 then 1 + 2*f(n/2)
    else 2*f(n/2)
}

// <vc-helpers>
lemma f_expand(n: nat)
    decreases n
    ensures f(n) == (if n == 0 then 1 else if n % 2 == 0 then 1 + 2 * f(n/2) else 2 * f(n/2))
{
    // The ensures clause follows directly from the function definition
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method mod(n:nat) returns (a:nat) 
ensures a == f(n)
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    a := 1;
  } else {
    var half := n/2;
    var sub_result := mod(half);
    if n % 2 == 0 {
      a := 2 * sub_result + 1;
    } else {
      a := 2 * sub_result;
    }
  }
}
// </vc-code>

