method mystery1(n: nat,m: nat) returns (res: nat)
  ensures n+m == res
{
  if (n==0) {
    return m;
  }
  else {
    var aux := mystery1 (n-1,m);
    return 1+aux;
  }
}

// <vc-helpers>
// </vc-helpers>

method mystery2(n: nat,m: nat) returns (res: nat)
  ensures n*m == res
// </vc-spec>
// <vc-code>
{
  if (n == 0) {
    return 0;
  }
  else {
    var aux := mystery2(n-1, m);
    var sum := mystery1(aux, m);
    return sum;
  }
}
// </vc-code>

// 5a

// 5b

// 5c
// pode dar false e eles nao serem iguais
// 

// 5d