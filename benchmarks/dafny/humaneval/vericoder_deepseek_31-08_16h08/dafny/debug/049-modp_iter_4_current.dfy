function modp_rec(n: int, p: int): int
  requires p > 0
  requires n >= 0
{
    if n == 0 then 1 % p else (modp_rec(n - 1, p) * 2) % p
}

// <vc-helpers>
lemma modp_rec_lemma(n: int, p: int)
  requires p > 0
  requires n >= 0
  ensures modp_rec(n, p) == pow(2, n) % p
  decreases n
{
  if n == 0 {
    assert pow(2, 0) == 1;
  } else {
    modp_rec_lemma(n - 1, p);
    calc {
      modp_rec(n, p);
      == // def modp_rec
      (modp_rec(n - 1, p) * 2) % p;
      == { modp_rec_lemma(n - 1, p); }
      ((pow(2, n - 1) % p) * 2) % p;
      == // modular arithmetic property
      (pow(2, n - 1) * 2) % p;
      == { assert pow(2, n) == pow(2, n - 1) * 2; }
      pow(2, n) % p;
    }
  }
}

function pow(base: int, exp: int): int
  requires exp >= 0
  decreases exp
{
  if exp == 0 then 1 else base * pow(base, exp - 1)
}
// </vc-helpers>

// <vc-spec>
method modp(n: int, p: int) returns (r: int)
  // pre-conditions-start
  requires p > 0
  requires n >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures r == modp_rec(n, p)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var power := 1;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant power == pow(2, i) % p
  {
    calc {
      (power * 2) % p;
      == { assert power == pow(2, i) % p; }
      ((pow(2, i) % p) * 2) % p;
      == // modular arithmetic property
      (pow(2, i) * 2) % p;
      == { assert pow(2, i) * 2 == pow(2, i + 1); }
      pow(2, i + 1) % p;
    }
    power := (power * 2) % p;
    i := i + 1;
  }
  modp_rec_lemma(n, p);
  r := power;
}
// </vc-code>

