// <vc-preamble>
function ListToNat(l: seq<nat>): nat
    decreases |l|
{
    if |l| == 0 then
        0
    else
        l[0] + 10 * ListToNat(l[1..])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): DivMod10: decomposition of n into quotient*10 + remainder */
lemma DivMod10(n: nat)
    ensures n == (n / 10) * 10 + n % 10 && n % 10 < 10
{
    assert n == (n / 10) * 10 + n % 10;
    assert n % 10 < 10;
}

/* helper modified by LLM (iteration 5): DigitSumBound: bounds for digit addition with carry */
lemma DigitSumBound(a: nat, b: nat, c: nat)
    requires a < 10 && b < 10 && c <= 1
    ensures a + b + c == ((a + b + c) / 10) * 10 + (a + b + c) % 10 && (a + b + c) % 10 < 10 && (a + b + c) / 10 <= 1
{
    var s := a + b + c;
    assert s <= 19;
    DivMod10(s);
    assert s / 10 <= 1;
}

/* helper modified by LLM (iteration 5): Pow10 function for powers of 10 */
function Pow10(n: nat): nat
    decreases n
{
    if n == 0 then 1 else 10 * Pow10(n - 1)
}

/* helper modified by LLM (iteration 5): Pow10_mul: relation Pow10(n+1) == 10 * Pow10(n) */
lemma Pow10_mul(n: nat)
    ensures Pow10(n + 1) == 10 * Pow10(n)
    decreases n
{
    if n == 0 {
        assert Pow10(1) == 10 * Pow10(0);
    } else {
        Pow10_mul(n - 1);
        assert Pow10(n + 1) == 10 * Pow10(n);
    }
}

/* helper modified by LLM (iteration 5): AppendDigit: relate ListToNat after appending a digit */
lemma AppendDigit(temp: seq<nat>, d: nat)
    requires d < 10
    ensures ListToNat(temp + [d]) == ListToNat(temp) + d * Pow10(|temp|)
    decreases |temp|
{
    if |temp| == 0 {
        assert ListToNat([d]) == d;
        assert Pow10(0) == 1;
        assert ListToNat([d]) == 0 + d * Pow10(0);
    } else {
        AppendDigit(temp[1..], d);
        Pow10_mul(|temp| - 1);
        assert (temp + [d])[0] == temp[0];
        assert (temp + [d])[1..] == temp[1..] + [d];
        assert ListToNat(temp + [d]) == (temp + [d])[0] + 10 * ListToNat((temp + [d])[1..]);
        assert ListToNat(temp + [d]) == temp[0] + 10 * ListToNat(temp[1..] + [d]);
        assert ListToNat(temp[1..] + [d]) == ListToNat(temp[1..]) + d * Pow10(|temp| - 1);
        assert Pow10(|temp|) == 10 * Pow10(|temp| - 1);
        assert temp[0] + 10 * (ListToNat(temp[1..]) + d * Pow10(|temp| - 1)) == (temp[0] + 10 * ListToNat(temp[1..])) + d * Pow10(|temp|);
        assert ListToNat(temp) == temp[0] + 10 * ListToNat(temp[1..]);
        assert ListToNat(temp + [d]) == ListToNat(temp) + d * Pow10(|temp|);
    }
}

// </vc-helpers>

// <vc-spec>
method AddTwoNumbers(l1: array<nat>, l2: array<nat>) returns (result: array<nat>)
    requires 
        l1.Length > 0 &&
        l2.Length > 0 &&
        (forall i :: 0 <= i < l1.Length ==> l1[i] < 10) &&
        (forall i :: 0 <= i < l2.Length ==> l2[i] < 10) &&
        (l1[l1.Length - 1] != 0 || (l1.Length == 1 && l1[0] == 0)) &&
        (l2[l2.Length - 1] != 0 || (l2.Length == 1 && l2[0] == 0))
    ensures
        result.Length > 0 &&
        ListToNat(result[..]) == ListToNat(l1[..]) + ListToNat(l2[..]) &&
        (forall i :: 0 <= i < result.Length ==> result[i] < 10) &&
        (result[result.Length - 1] != 0 || (l1.Length == 1 && l1[0] == 0 && l2.Length == 1 && l2[0] == 0 && result.Length == 1 && result[0] == 0))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): digitwise addition using sequences and simpler invariant */
  var s1 := l1[..];
  var s2 := l2[..];
  var n1 := s1.Length;
  var n2 := s2.Length;
  var nmax := if n1 > n2 then n1 else n2;
  var temp := new nat[nmax + 1];
  var i := 0;
  var carry: nat := 0;
  var pow: nat := 1;
  while i < nmax
    invariant 0 <= i <= nmax
    invariant carry <= 1
    invariant pow == Pow10(i)
    invariant (forall j :: 0 <= j < i ==> temp[j] < 10)
    invariant ListToNat(temp[..i]) + pow * (ListToNat(s1[i..]) + ListToNat(s2[i..]) + carry) == ListToNat(s1) + ListToNat(s2)
  {
    var ai := if i < n1 then s1[i] else 0;
    var bi := if i < n2 then s2[i] else 0;
    var s := ai + bi + carry;
    DigitSumBound(ai, bi, carry);
    temp[i] := s % 10;
    carry := s / 10;
    pow := pow * 10;
    i := i + 1;
  }
  var len := if carry == 0 then nmax else nmax + 1;
  if carry != 0 {
    temp[nmax] := carry;
  }
  result := new nat[len];
  var k := 0;
  while k < len
    invariant 0 <= k <= len
    invariant (forall j :: 0 <= j < k ==> result[j] == temp[j])
  {
    result[k] := temp[k];
    k := k + 1;
  }
  if carry == 0 {
    // no final carry: remaining slices are empty so sum matches
    assert ListToNat(s1[nmax..]) == 0;
    assert ListToNat(s2[nmax..]) == 0;
    assert ListToNat(result[..]) == ListToNat(temp[..nmax]);
    assert ListToNat(result[..]) == ListToNat(s1) + ListToNat(s2);
  } else {
    AppendDigit(temp[..nmax], carry);
    assert ListToNat(temp[..nmax + 1]) == ListToNat(temp[..nmax]) + carry * Pow10(nmax);
    assert ListToNat(result[..]) == ListToNat(temp[..nmax + 1]);
    assert ListToNat(result[..]) == ListToNat(s1) + ListToNat(s2);
  }
}

// </vc-code>
