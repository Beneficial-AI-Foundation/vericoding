// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): added min helper */
function min(a:int, b:int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
function last_digit(n: nat): nat
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): return n modulo 10 as last digit */
  n % 10
}

lemma last_digit_correct(n: nat)
    ensures
        last_digit(n) < 10
    ensures
        last_digit(n) == n % 10
{
  /* code modified by LLM (iteration 4): proof by unfolding definition and modulo bound */
  assert last_digit(n) == n % 10;
  assert n % 10 < 10;
  assert last_digit(n) < 10;
}

// </vc-code>
