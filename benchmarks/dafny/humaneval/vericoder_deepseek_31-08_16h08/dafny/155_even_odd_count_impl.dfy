

// <vc-helpers>
lemma even_odd_recursion(n: nat)
  requires n > 0
  ensures even_count(n) == even_count(n / 10) + (1 - n % 2)
  ensures odd_count(n) == odd_count(n / 10) + n % 2
{
  // The function definitions themselves provide the recursion equations
}

lemma even_odd_count_base()
  ensures even_count(0) == 0 && odd_count(0) == 0
{
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
  if n == 0 {
    even := 0;
    odd := 0;
  } else {
    if n / 10 == 0 {
      var e: nat, o: nat := 0, 0;
      even := e + (1 - n % 2);
      odd := o + n % 2;
    } else {
      var e, o := even_odd_count(n / 10);
      even := e + (1 - n % 2);
      odd := o + n % 2;
    }
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