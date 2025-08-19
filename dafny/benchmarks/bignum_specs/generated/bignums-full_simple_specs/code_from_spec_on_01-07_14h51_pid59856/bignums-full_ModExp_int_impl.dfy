//ATOM

// computes res := x^y
opaque function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}

//ATOM

// computes res := x^y % z when y == 2^n (repeated squaring)
method ModExpPow2_int(x: nat, y:nat, n:nat, z: nat) returns (res:nat)
  requires y == Exp_int(2, n)
  requires z > 0
  ensures res == Exp_int(x,y) % z
  decreases n
{
    res := 0;
    assume res == Exp_int(x,y) % z;
    return res;
}

//IMPL ModExp_int

// simulates the exponentiation we do on bistrings through bit decomposition and repeated squaring
method ModExp_int(x: nat, y:nat, n:nat, z: nat) returns (res:nat)
  requires y < Exp_int(2,n+1)
  requires z > 1 //&& n > 0
  ensures res == Exp_int(x,y) % z
  decreases n
{
    if y == 0 {
        /* code modified by LLM (iteration 1): Added assertion to help prove x^0 = 1 */
        assert Exp_int(x, 0) == 1 by { reveal Exp_int(); }
        res := 1;
    } else if n == 0 {
        // y < 2^1 = 2, and y != 0, so y == 1
        /* code modified by LLM (iteration 1): Added assertions to prove y == 1 when n == 0 */
        assert Exp_int(2, 1) == 2 by { reveal Exp_int(); }
        assert y < 2 && y != 0;
        assert y == 1;
        assert Exp_int(x, 1) == x by { reveal Exp_int(); }
        res := x % z;
    } else {
        /* code modified by LLM (iteration 1): Fixed power of 2 calculation and bounds checking */
        assert Exp_int(2, n+1) == 2 * Exp_int(2, n) by { reveal Exp_int(); }
        var pow2n := Exp_int(2, n);
        if y < pow2n {
            // y is in lower half, recurse with n-1
            /* code modified by LLM (iteration 1): Fixed precondition proof for recursive call */
            assert n > 0;
            assert Exp_int(2, n) == 2 * Exp_int(2, n-1) by { reveal Exp_int(); }
            assert y < pow2n;
            assert pow2n == 2 * Exp_int(2, n-1);
            assert y < 2 * Exp_int(2, n-1);
            assert y < Exp_int(2, (n-1)+1);
            res := ModExp_int(x, y, n-1, z);
        } else {
            // y >= 2^n, so y = 2^n + remainder
            var remainder := y - pow2n;
            /* code modified by LLM (iteration 1): Fixed remainder bounds proof */
            assert remainder < pow2n by {
                assert y < Exp_int(2, n+1);
                assert Exp_int(2, n+1) == 2 * Exp_int(2, n) by { reveal Exp_int(); }
                assert y < 2 * pow2n;
                assert y >= pow2n;
                assert remainder == y - pow2n < 2 * pow2n - pow2n;
                assert remainder < pow2n;
            }
            assert n > 0;
            /* code modified by LLM (iteration 1): Fixed bound for recursive call */
            assert pow2n == Exp_int(2, n);
            assert Exp_int(2, n) == 2 * Exp_int(2, n-1) by { reveal Exp_int(); }
            assert remainder < pow2n;
            assert pow2n == 2 * Exp_int(2, n-1);
            assert remainder < 2 * Exp_int(2, n-1);
            assert remainder < Exp_int(2, (n-1)+1);
            var pow_remainder := ModExp_int(x, remainder, n-1, z);
            var pow_2n := ModExpPow2_int(x, pow2n, n, z);
            /* code modified by LLM (iteration 1): Added complete proof of exponentiation property */
            assert y == pow2n + remainder;
            assert Exp_int(x, y) == Exp_int(x, pow2n + remainder);
            ExpAdditive(x, pow2n, remainder);
            assert Exp_int(x, pow2n + remainder) == Exp_int(x, pow2n) * Exp_int(x, remainder);
            /* code modified by LLM (iteration 1): Fixed modular arithmetic with proper lemma */
            assert pow_remainder == Exp_int(x, remainder) % z;
            assert pow_2n == Exp_int(x, pow2n) % z;
            ModMultLemma(Exp_int(x, pow2n), Exp_int(x, remainder), z);
            res := (pow_2n * pow_remainder) % z;
            assert res == (Exp_int(x, pow2n) * Exp_int(x, remainder)) % z;
            assert res == Exp_int(x, y) % z;
        }
    }
}

/* code modified by LLM (iteration 1): Added helper lemma for exponentiation additivity */
lemma ExpAdditive(x: nat, a: nat, b: nat)
  ensures Exp_int(x, a + b) == Exp_int(x, a) * Exp_int(x, b)
  decreases b
{
  reveal Exp_int();
  if b == 0 {
    assert Exp_int(x, b) == 1;
    assert Exp_int(x, a + b) == Exp_int(x, a);
  } else {
    calc {
      Exp_int(x, a + b);
      == x * Exp_int(x, (a + b) - 1);
      == { assert (a + b) - 1 == a + (b - 1); }
      x * Exp_int(x, a + (b - 1));
      == { ExpAdditive(x, a, b - 1); }
      x * (Exp_int(x, a) * Exp_int(x, b - 1));
      == { /* associativity of multiplication */ }
      (x * Exp_int(x, b - 1)) * Exp_int(x, a);
      == { assert x * Exp_int(x, b - 1) == Exp_int(x, b); }
      Exp_int(x, b) * Exp_int(x, a);
      == { /* commutativity of multiplication */ }
      Exp_int(x, a) * Exp_int(x, b);
    }
  }
}

/* code modified by LLM (iteration 1): Modular multiplication lemma with complete proof */
lemma ModMultLemma(a: nat, b: nat, m: nat)
  requires m > 0
  ensures ((a % m) * (b % m)) % m == (a * b) % m
{
  var a_mod := a % m;
  var b_mod := b % m;
  var a_div := a / m;
  var b_div := b / m;
  
  assert a == a_div * m + a_mod;
  assert b == b_div * m + b_mod;
  
  calc {
    a * b;
    == (a_div * m + a_mod) * (b_div * m + b_mod);
    == { /* expand multiplication */ }
    a_div * m * b_div * m + a_div * m * b_mod + a_mod * b_div * m + a_mod * b_mod;
    == { /* factor out m */ }
    m * (a_div * b_div * m + a_div * b_mod + a_mod * b_div) + a_mod * b_mod;
  }
  
  assert (a * b) % m == (a_mod * b_mod) % m;
  assert ((a % m) * (b % m)) % m == (a_mod * b_mod) % m;
  assert ((a % m) * (b % m)) % m == (a * b) % m;
}