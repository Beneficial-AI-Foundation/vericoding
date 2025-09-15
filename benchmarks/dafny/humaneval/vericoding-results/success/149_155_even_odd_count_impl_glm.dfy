// <vc-preamble>
function odd_count(n: nat): nat {
  if n == 0 then 0
  else odd_count(n / 10) + n % 2
}
function even_count(n: nat): nat
{
  if n == 0 then 0
  else even_count(n / 10) + (1 - n % 2)
}
// </vc-preamble>

// <vc-helpers>
function even_odd_pair(n: nat): (nat, nat) {
  if n == 0 then (0, 0)
  else 
    var pair := even_odd_pair(n / 10);
    (pair.0 + (1 - n % 2), pair.1 + n % 2)
}

lemma even_odd_pair_correct(n: nat)
  ensures even_odd_pair(n) == (even_count(n), odd_count(n))
{
  if n == 0 {
  } else {
    calc {
      even_odd_pair(n);
      == { reveal even_odd_pair; }
         (even_odd_pair(n/10).0 + (1 - n%2), even_odd_pair(n/10).1 + n%2);
      == { even_odd_pair_correct(n/10); }
         (even_count(n/10) + (1 - n%2), odd_count(n/10) + n%2);
      == { reveal even_count(); reveal odd_count(); }
         (even_count(n), odd_count(n));
    }
  }
}
// </vc-helpers>

// <vc-spec>
method even_odd_count(n: nat) returns (even: nat, odd: nat)

  requires n > 0

  ensures even == even_count(n)
  ensures odd == odd_count(n)
// </vc-spec>
// <vc-code>
{
  var pair := even_odd_pair(n);
  even_odd_pair_correct(n);
  even := pair.0;
  odd := pair.1;
}
// </vc-code>
