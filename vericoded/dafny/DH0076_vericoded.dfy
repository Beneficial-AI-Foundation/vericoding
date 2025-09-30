// <vc-preamble>

predicate is_prime_number(n: int)
{
  n >= 2 && forall k: int :: 2 <= k < n ==> n % k != 0
}

function seq_product(factors: seq<int>): int
  decreases |factors|
{
  if |factors| == 0 then 1
  else factors[0] * seq_product(factors[1..])
}

function power(base: int, exp: nat): int
  decreases exp
{
  if exp == 0 then 1
  else base * power(base, exp - 1)
}

lemma seq_product_append_lemma(s: seq<int>, x: int)
  ensures seq_product(s + [x]) == seq_product(s) * x
{
  if |s| == 0 {
    assert s + [x] == [x];
    assert seq_product([x]) == x;
    assert seq_product(s) == 1;
  } else {
    assert s == [s[0]] + s[1..];
    assert s + [x] == [s[0]] + (s[1..] + [x]);
    seq_product_append_lemma(s[1..], x);
    assert seq_product(s[1..] + [x]) == seq_product(s[1..]) * x;
    assert seq_product(s + [x]) == s[0] * seq_product(s[1..] + [x]);
    assert seq_product(s + [x]) == s[0] * (seq_product(s[1..]) * x);
    assert seq_product(s + [x]) == (s[0] * seq_product(s[1..])) * x;
    assert seq_product(s + [x]) == seq_product(s) * x;
  }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method is_multiply_prime(a: int) returns (result: bool)
  requires a >= 0 && a < 100
  ensures a < 8 ==> result == false
  ensures result == true <==> (exists p1: int, p2: int, p3: int :: 
    p1 >= 2 && p2 >= 2 && p3 >= 2 && 
    is_prime_number(p1) && is_prime_number(p2) && is_prime_number(p3) &&
    a == p1 * p2 * p3)
// </vc-spec>
// <vc-code>
{
  if a < 8 {
    result := false;
    return;
  }
  
  result := false;
  
  var p1 := 2;
  while p1 * 4 <= a
    invariant p1 >= 2
    invariant result == true <==> (exists q1: int, q2: int, q3: int :: 
      q1 >= 2 && q2 >= 2 && q3 >= 2 && q1 < p1 &&
      is_prime_number(q1) && is_prime_number(q2) && is_prime_number(q3) &&
      a == q1 * q2 * q3)
  {
    if is_prime_number(p1) {
      var p2 := 2;
      while p1 * p2 * 2 <= a
        invariant p2 >= 2
        invariant result == true <==> (exists q1: int, q2: int, q3: int :: 
          q1 >= 2 && q2 >= 2 && q3 >= 2 && 
          ((q1 < p1) || (q1 == p1 && q2 < p2)) &&
          is_prime_number(q1) && is_prime_number(q2) && is_prime_number(q3) &&
          a == q1 * q2 * q3)
      {
        if is_prime_number(p2) {
          if a % (p1 * p2) == 0 {
            var p3 := a / (p1 * p2);
            if p3 >= 2 && is_prime_number(p3) {
              result := true;
              return;
            }
          }
        }
        p2 := p2 + 1;
      }
    }
    p1 := p1 + 1;
  }
}
// </vc-code>
