//ATOM

predicate ValidBitString(s: string) {
  forall i :: 0 <= i < |s| ==> s[i] == '0' || s[i] == '1'
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

//IMPL 
    
method Main() {
    /* code modified by LLM (iteration 1): Added complete implementation with binary string operations demonstration */
    print "Binary string operations program\n";
    
    var s1 := "101";  // binary for 5
    var s2 := "11";   // binary for 3
    
    var sum := Add(s1, s2);
    print "Addition: ", s1, " + ", s2, " = ", sum, "\n";
    
    var diff := Sub(s1, s2);
    print "Subtraction: ", s1, " - ", s2, " = ", diff, "\n";
    
    var product := Mul(s1, s2);
    print "Multiplication: ", s1, " * ", s2, " = ", product, "\n";
    
    var converted := Int2Str(7);
    print "Int2Str(7) = ", converted, "\n";
    
    var converted_back := Str2Int("111");
    print "Str2Int(\"111\") = ", converted_back, "\n";
}