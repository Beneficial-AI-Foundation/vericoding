// <vc-preamble>
//PRE-CONDITIONS -> REQUIRES
//POST-CONDITIONS -> ENSURES



// 3
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
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method mystery2(n: nat,m: nat) returns (res: nat)
  ensures n*m == res
// </vc-spec>
// <vc-code>
{
  if (n==0) {
    return 0;
  }
  else {
    var aux := mystery2(n-1,m);
    var aux2 := mystery1(m,aux);
    return aux2;
  }
}
// </vc-code>

// 5a

// 5b

// 5c
// pode dar false e eles nao serem iguais
// 

// 5d