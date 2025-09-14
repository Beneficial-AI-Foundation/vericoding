ghost function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}
predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}
ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
function ModExp(base: nat, exp: nat, modulus: nat): nat
  requires modulus > 1
  decreases exp
{
  if exp == 0 then 1
  else if exp % 2 == 0 then
    (ModExp(base, exp / 2, modulus) * ModExp(base, exp / 2, modulus)) % modulus
  else
    (base * ModExp(base, exp - 1, modulus)) % modulus
}

// Lemma to connect Exp_int to natural numbers for ModExp
lemma ExpToInt(x: nat, y: nat) returns (res: nat)
  ensures Exp_int(x, y) == res
  decreases y
{
  if y == 0 {
    return 1;
  } else {
    var prev_res := ExpToInt(x, y - 1);
    return x * prev_res;
  }
}

// Lemma to show that Str2Int properties are useful for ModExpPow2
lemma Str2IntProps(s: string)
  requires ValidBitString(s)
  ensures Str2Int(s) >= 0
{}

// Helper to convert nat to bitstring for Add method (not provided, but assumed)
// This is a placeholder since the 'Add' method itself is assumed, so is this helper for it.
// In a real scenario, this would be part of the 'Add' module or a global utility.
function nat_to_bitstring(val: nat): string
{
  if val == 0 then "0"
  else
    var s := "";
    var current_val := val;
    while current_val > 0
      invariant current_val >= 0
      invariant ValidBitString(s)
      invariant Str2Int(nat_to_bitstring_rev(current_val, s)) == val
      decreases current_val
    {
      if current_val % 2 == 1 {
        s := "1" + s;
      } else {
        s := "0" + s;
      }
      current_val := current_val / 2;
    }
    s
}

ghost function nat_to_bitstring_rev(current_val: nat, s: string): string
{
  if current_val == 0 then s
  else nat_to_bitstring_rev(current_val / 2, (if current_val % 2 == 1 then "1" else "0") + s)
}
// </vc-helpers>

// <vc-spec>
method ModExpPow2(sx: string, sy: string, n: nat, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  // sy is power of 2 or zero
  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| == n+1
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases n
// </vc-spec>
// <vc-code>
{
  var x_int := Str2Int(sx);
  var y_int := Str2Int(sy);
  var z_int := Str2Int(sz);

  if y_int == 0 {
    res := "1"; // x^0 = 1
  } else if n == 0 { // sy is 1 (2^0)
    res := nat_to_bitstring(x_int % z_int);
  } else {
    // inductive step: y_int = 2^n
    // x^(2^n) % z = (x^(2^(n-1)))^2 % z

    var sy_half_string: string := "1"; // "1" represents 2^0
    var k := 0;
    while k < n - 1
      invariant 0 <= k <= n - 1
      invariant ValidBitString(sy_half_string)
      invariant Str2Int(sy_half_string) == Exp_int(2, k + 1)
      invariant |sy_half_string| == k + 2
      decreases n - 1 - k
    {
      sy_half_string := sy_half_string + "0";
      k := k + 1;
    }
    // Now sy_half_string should represent 2^(n-1) with length n.
    // When n=1, k will be 0, loop won't run, sy_half_string remains "1".
    // 2^(1-1) = 2^0 = 1. Length 0+2=2. This is correct for n=1,
    // where sy_half_string should be "01" (length 2 representing 1)
    // or just "1" (length 1 representing 1).
    // The `n+1` length check in precondition for sy implies leading zeros matter.

    // Adjust for n=1 case: if n=1, sy_half_string should represent 2^0, which is "1".
    // The loop initializes sy_half_string to "1". If n-1 == 0, the loop condition (k < n-1) is false from the start.
    // So for n=1, sy_half_string remains "1".
    // Its Str2Int is 1 (2^0). Its length is 1.
    // The recursive call expects sy string of length (n-1)+1.
    // For n=1, it's (1-1)+1 = 1. So "1" is fine.
    // For n=2, loop runs for k=0. sy_half_string becomes "10". This is 2^1. Length 2.
    // Expected length for 2^(2-1) = 2^1 is (2-1)+1 = 2. So "10" is fine.

    // If n==0, (already handled)
    // If n > 0, then n-1 >= 0.
    // The recursive call ModExpPow2(sx, sy_half_string, n - 1, sz) requires:
    // Str2Int(sy_half_string) == Exp_int(2, n - 1)
    // |sy_half_string| == (n - 1) + 1 .

    // The length of sy_half_string is k+2. When the loop finishes, k = n-2.
    // (If n-1 > 0, Loop runs for k = 0, ..., n-2. So k finishes at n-2).
    // If n-1 == 0 (i.e. n=1), then loop doesn't run, k remains 0. sy_half_string is "1".
    // Its length is 1. And 1 == (n-1)+1. Correct.
    // If n>1, loop runs till k = n-2. |sy_half_string| (at start of loop) = k+2.
    // (after loop, k is no longer relevant for the length - it's sy_half_string's length that matters).
    // The loop adds n-1-k "0"s to sy_half_string where k starts at 0.
    // If n=2, k=0. loop runs once, sy_half_string = "10". |sy_half_string|=2. Correct.
    // If n=3, k=0. Loop runs twice. sy_half_string: "1" -> "10" -> "100". |sy_half_string|=3. Correct.
    // This implies that |sy_half_string| will be n.
    // For sy_half_string to represent 2^(n-1), its length should be (n-1)+1 = n. This matches.

    // Str2Int(sy_half_string) needs to be 2^(n-1).
    // Initial: sy_half_string = "1", Str2Int("1") = 1 = 2^0.
    // Loop: Each time, `sy_half_string := sy_half_string + "0"`. This means `Str2Int(new) = 2 * Str2Int(old)`.
    // The loop runs `n-1` times. So Str2Int will be `1 * 2^(n-1) = 2^(n-1)`.
    assert Str2Int(sy_half_string) == Exp_int(2, n - 1);
    assert |sy_half_string| == (n - 1) + 1;

    var res_half_exp_str := ModExpPow2(sx, sy_half_string, n - 1, sz);
    var res_half_exp_int := Str2Int(res_half_exp_str);

    var final_val := (res_half_exp_int * res_half_exp_int) % z_int;
    res := nat_to_bitstring(final_val);
  }
}
// </vc-code>

