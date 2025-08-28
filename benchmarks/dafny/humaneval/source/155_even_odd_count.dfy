method even_odd_count(n: nat) returns (even: nat, odd: nat)
  // pre-conditions-start
  requires n > 0
  // pre-conditions-end
  // post-conditions-start
  ensures even == even_count(n)
  ensures odd == odd_count(n)
  // post-conditions-end
{
  // impl-start
  var num := n;

  even := 0;
  odd := 0;
  while num > 0
    // invariants-start
    invariant even + even_count(num) == even_count(n)
    invariant odd + odd_count(num) == odd_count(n)
    // invariants-end
  {
    even := even + (1 - num % 2);
    odd := odd + num % 2;
    num := num / 10;
  }
  // impl-end
}

function odd_count(n: nat): nat {
  if n == 0 then 0
  else odd_count(n / 10) + n % 2
}
// pure-end
function even_count(n: nat): nat
{
  if n == 0 then 0
  else even_count(n / 10) + (1 - n % 2)
}
// pure-end
