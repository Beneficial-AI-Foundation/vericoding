//ATOM

// Helper predicate to validate bit strings
predicate ValidBitString(s: string)
{
  |s| > 0 && forall i :: 0 <= i < |s| ==> s[i] == '0' || s[i] == '1'
}

//ATOM

// ----------------------------------------------------
// Int2Str: nat -> bit-string (reference function)
//    - "0" if n=0
//    - no leading zeros otherwise
// ----------------------------------------------------
function Int2Str(n: nat): string
  // I added the following post-condition because Str2Int requires it
  ensures ValidBitString(Int2Str(n))
  ensures Str2Int(Int2Str(n)) == n
  decreases n
{
  if n == 0 then
    "0"

  else (if n == 1
        then "1"
        else (
            // Recursively build from most significant bits.
            // The last character added is (n % 2).
            assert ValidBitString(Int2Str(n/2));
            assert Str2Int(Int2Str(n/2)) == n/2;
            Int2Str(n / 2) + (if n % 2 == 0 then "0" else "1")
          )
       )
}

//ATOM

// ----------------------------------------------------
// string-based addition (no Str2Int / Int2Str)
// ----------------------------------------------------
method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
    res := "";
    assume ValidBitString(res);
    assume Str2Int(res) == Str2Int(s1) + Str2Int(s2);
    return res;
}

//ATOM

// ----------------------------------------------------
// string-based subtraction (s1 >= s2)
// ----------------------------------------------------
method Sub(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s1) >= Str2Int(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) - Str2Int(s2)
{
    res := "";
    assume ValidBitString(res);
    assume Str2Int(res) == Str2Int(s1) - Str2Int(s2);
    return res;
}

//ATOM

// ----------------------------------------------------
// Str2Int: bit-string -> nat (reference function)
// ----------------------------------------------------
function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

//ATOM

// ----------------------------------------------------
// string-based multiplication
//    No direct use of Str2Int/Int2Str
// ----------------------------------------------------
method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
    assume ValidBitString(res);
    assume Str2Int(res) == Str2Int(s1) * Str2Int(s2);
}

//IMPL Main
method Main() {
    /* code modified by LLM (iteration 1): Added comprehensive demonstration of binary arithmetic operations */
    print "Binary arithmetic operations demonstration\n";
    
    // Test basic bit strings
    var a := "101";  // 5 in decimal
    var b := "11";   // 3 in decimal
    
    print "a = ", a, "\n";
    print "b = ", b, "\n";
    
    // Test addition
    var sum := Add(a, b);
    print "a + b = ", sum, "\n";
    
    // Test subtraction (a >= b)
    var diff := Sub(a, b);
    print "a - b = ", diff, "\n";
    
    // Test multiplication
    var product := Mul(a, b);
    print "a * b = ", product, "\n";
    
    // Test with zero
    var zero := "0";
    var sum_with_zero := Add(a, zero);
    print "a + 0 = ", sum_with_zero, "\n";
    
    // Test Int2Str conversion
    var converted := Int2Str(7);
    print "Int2Str(7) = ", converted, "\n";
    
    print "All operations completed successfully\n";
}