//ATOM

predicate ValidBitString(s: string)
{
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
    var s1 := "101";  // binary for 5
    var s2 := "11";   // binary for 3
    
    /* code modified by LLM (iteration 1): Add comprehensive validity proofs for s1 and s2 */
    assert |s1| == 3;
    assert s1[0] == '1' && s1[1] == '0' && s1[2] == '1';
    assert forall i :: 0 <= i < |s1| ==> s1[i] == '0' || s1[i] == '1';
    assert ValidBitString(s1);
    
    assert |s2| == 2;
    assert s2[0] == '1' && s2[1] == '1';
    assert forall i :: 0 <= i < |s2| ==> s2[i] == '0' || s2[i] == '1';
    assert ValidBitString(s2);
    
    // Test addition
    var sum := Add(s1, s2);
    
    /* code modified by LLM (iteration 1): Compute and assert specific values for subtraction precondition */
    assert Str2Int(s1) == 5;  // "101" = 5
    assert Str2Int(s2) == 3;  // "11" = 3
    assert Str2Int(s1) >= Str2Int(s2);
    
    // Test subtraction (5 >= 3, so this should be valid)
    var diff := Sub(s1, s2);
    
    // Test multiplication
    var product := Mul(s1, s2);
    
    // Test conversion functions
    var str := Int2Str(7);
    
    var testStr := "111";
    /* code modified by LLM (iteration 1): Add comprehensive validity proof for testStr */
    assert |testStr| == 3;
    assert testStr[0] == '1' && testStr[1] == '1' && testStr[2] == '1';
    assert forall i :: 0 <= i < |testStr| ==> testStr[i] == '0' || testStr[i] == '1';
    assert ValidBitString(testStr);
    var num := Str2Int(testStr);
    
    print "Addition result: ", sum, "\n";
    print "Subtraction result: ", diff, "\n";
    print "Multiplication result: ", product, "\n";
    print "Int2Str(7): ", str, "\n";
    print "Str2Int(\"111\"): ", num, "\n";
}