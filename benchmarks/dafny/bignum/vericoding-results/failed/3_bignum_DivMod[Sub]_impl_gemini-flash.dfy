ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}
predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

method Sub(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s1) >= Str2Int(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) - Str2Int(s2)
{
  assume{:axiom} false;
}

// <vc-helpers>
function Multiply(s: string, n: nat): string
  requires ValidBitString(s)
  requires n >= 0
  ensures ValidBitString(Multiply(s, n))
  ensures Str2Int(Multiply(s, n)) == Str2Int(s) * n
{
  if n == 0 then
    "0"
  else if n == 1 then
    s
  else if n % 2 == 0 then
    Add(Multiply(s, n / 2), Multiply(s, n / 2))
  else
    Add(Add(Multiply(s, n / 2), Multiply(s, n / 2)), "1")
}

function Add(s1: string, s2: string): string
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(Add(s1, s2))
  ensures Str2Int(Add(s1, s2)) == Str2Int(s1) + Str2Int(s2)
{
  var n1 := Str2Int(s1);
  var n2 := Str2Int(s2);
  var sum := n1 + n2;
  return Int2Str(sum);
}

function Int2Str(n: nat): string {
  if n == 0 then
    "0"
  else
  {
    var s := "";
    var temp := n;
    while temp > 0
      invariant temp >= 0
      invariant ValidBitString(s)
      invariant n == (temp * (2 as nat raised to |s|)) + Str2Int(s)
      decreasing temp
    {
      s := (if temp % 2 == 1 then "1" else "0") + s;
      temp := temp / 2;
    }
    return s;
  }
}

ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}
predicate ValidBitString(s: string)
{
  // All characters must be '0' or '1'.
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

method Sub(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s1) >= Str2Int(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) - Str2Int(s2)
{
  var n1 := Str2Int(s1);
  var n2 := Str2Int(s2);
  var diff := n1 - n2;
  return Int2Str(diff);
}
// </vc-helpers>

// <vc-spec>
method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
// </vc-spec>
// <vc-code>
{
    var q_str := "0";
    var r_nat := 0; // Use nat representation for remainder

    var divisor_nat := Str2Int(divisor);

    // Initialize for the loop
    // var current_dividend_prefix := "0"; // This variable is not needed outside the loop

    var n_dividend := Str2Int(dividend);

    for i := 0 to |dividend|
        invariant 0 <= i <= |dividend|
        invariant ValidBitString(q_str)
        invariant r_nat >= 0
        invariant r_nat < divisor_nat * (2 as nat raised to (i - (if r_nat == 0 then 0 else (Str2Int(dividend[0..i]) / divisor_nat).ToString().Length))) // More precise bound derived from long division property
        invariant r_nat < divisor_nat || i == 0 // Added || i == 0 for initial state
        invariant (i == 0 ==> r_nat == 0) // Initially remainder is 0
        invariant (i > 0 ==> Str2Int(dividend[0..i]) == Str2Int(q_str) * divisor_nat + r_nat)
        invariant (i == 0 ==> n_dividend == Str2Int(q_str) * divisor_nat + Str2Int(dividend))
        invariant (i == |dividend| ==> Str2Int(dividend) == Str2Int(q_str) * divisor_nat + r_nat)
    {
        if i == 0 {
             // Initial step: Bring down the first bit if it makes sense, or treat it as 0
             // For the first iteration, we set current remainder.
             // This loop is designed to process bits one by one.
             // So, r_nat here represents the remainder of the prefix dividend[0..i]
             // when divided by divisor_nat.
             if |dividend| > 0 {
                 r_nat := (if dividend[0] == '1' then 1 else 0);
             } else {
                 r_nat := 0;
             }
        } else {
            // Bring down the next bit and append it to the remainder
            var current_bit := (if dividend[i-1] == '1' then 1 else 0); // Corrected index for current bit
            r_nat := r_nat * 2 + current_bit;

            // This ensures that current_dividend_prefix now represents dividend[0..i]
            // and the equation Str2Int(current_dividend_prefix) == Str2Int(q_str) * divisor_nat + r_nat
            // is maintained.
        }

        while r_nat >= divisor_nat
           invariant r_nat >= 0
           invariant r_nat < (2 as nat raised to (i + 1)) // Upper bound on r_nat
           invariant ValidBitString(q_str)
           invariant (n_dividend / (2 as nat raised to (|dividend|-i))) / divisor_nat == Str2Int(q_str) // More precise relationship
        {
            r_nat := r_nat - divisor_nat;
            q_str := Add(q_str, "1");
        }
        
        if i < |dividend| {
            q_str := Multiply(q_str, 2);
        }
    }
    return q_str, Int2Str(r_nat);
}
// </vc-code>

