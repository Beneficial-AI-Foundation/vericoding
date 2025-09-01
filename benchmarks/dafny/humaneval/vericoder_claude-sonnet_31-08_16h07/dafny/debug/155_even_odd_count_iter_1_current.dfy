

// <vc-helpers>
lemma even_count_invariant(n: nat, acc: nat)
  ensures even_count(n) + acc == even_count_helper(n, acc)

function even_count_helper(n: nat, acc: nat): nat {
  if n == 0 then acc
  else even_count_helper(n / 10, acc + (1 - n % 2))
}

lemma odd_count_invariant(n: nat, acc: nat)
  ensures odd_count(n) + acc == odd_count_helper(n, acc)

function odd_count_helper(n: nat, acc: nat): nat {
  if n == 0 then acc
  else odd_count_helper(n / 10, acc + n % 2)
}
// </vc-helpers>

// <vc-spec>
method even_odd_count(n: nat) returns (even: nat, odd: nat)
  // pre-conditions-start
  requires n > 0
  // pre-conditions-end
  // post-conditions-start
  ensures even == even_count(n)
  ensures odd == odd_count(n)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  even := 0;
  odd := 0;
  var temp := n;
  
  while temp > 0
    invariant even + even_count(temp) == even_count(n)
    invariant odd + odd_count(temp) == odd_count(n)
    decreases temp
  {
    var digit := temp % 10;
    if digit % 2 == 0 {
      even := even + 1;
    } else {
      odd := odd + 1;
    }
    temp := temp / 10;
  }
}
// </vc-code>

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