// ex3errors.dfy in Assignment 1
// verify that an array of characters is a Palindrome
/*
A Palindrome is a word that is the same when written forwards and when written backwards. 
For example, the word "refer" is a Palindrome.
The method PalVerify is supposed to verify whether a word is a Palindrome, 
where the word is represented as an array of characters. 
The method was written by a novice software engineer, and contains many errors.

   i) Without changing the signature or the code in the while loop, 
      fix the method so that it veriifes the code. Do not add any Dafny predicates or functions: 
      keep the changes to a minimum.

   ii) Write a tester method (you may call it anything you like) that verifies that the 
      testcases refer, z and the empty string are Palindromes, and xy and 123421 are not. 
      The tester should not generate any output.
*/

//IMPL PalVerify
method PalVerify(a: array<char>) returns (yn: bool)
ensures yn == true ==> forall i :: 0 <= i < a.Length/2 ==> a[i] == a[a.Length - i -1]
ensures yn == false ==> exists i :: 0 <= i < a.Length/2 && a[i] != a[a.Length - i -1]
ensures forall j :: 0<=j<a.Length ==> a[j] == old(a[j]) 
{
    var i := 0;
    yn := true;
    
    while i < a.Length / 2
        invariant 0 <= i <= a.Length / 2
        /* code modified by LLM (iteration 1): Fixed loop invariants to handle verification properly */
        invariant yn == true ==> forall k :: 0 <= k < i ==> a[k] == a[a.Length - k - 1]
        invariant yn == false ==> exists k :: 0 <= k < i && a[k] != a[a.Length - k - 1]
        invariant forall j :: 0 <= j < a.Length ==> a[j] == old(a[j])
    {
        if a[i] != a[a.Length - i - 1] {
            yn := false;
        }
        i := i + 1;
    }
}

//IMPL TEST
method TEST()
{
    // Test "refer" - should be palindrome
    var refer := new char[5];
    refer[0] := 'r'; refer[1] := 'e'; refer[2] := 'f'; refer[3] := 'e'; refer[4] := 'r';
    var result1 := PalVerify(refer);
    assert result1 == true;
    
    // Test "z" - should be palindrome
    var z := new char[1];
    z[0] := 'z';
    var result2 := PalVerify(z);
    assert result2 == true;
    
    // Test empty string - should be palindrome
    var empty := new char[0];
    var result3 := PalVerify(empty);
    assert result3 == true;
    
    // Test "xy" - should not be palindrome
    var xy := new char[2];
    xy[0] := 'x'; xy[1] := 'y';
    var result4 := PalVerify(xy);
    assert result4 == false;
    
    // Test "123421" - should not be palindrome
    var num := new char[6];
    num[0] := '1'; num[1] := '2'; num[2] := '3'; num[3] := '4'; num[4] := '2'; num[5] := '1';
    var result5 := PalVerify(num);
    assert result5 == false;
}